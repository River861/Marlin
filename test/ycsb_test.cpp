#include "Tree.h"
#include "Timer.h"

#include <stdlib.h>
#include <thread>
#include <time.h>
#include <vector>
#include <iostream>
#include <string>
#include <fstream>
#include <random>
#include <mutex>

#ifdef LONG_TEST_EPOCH
  #define TEST_EPOCH 40
  #define TIME_INTERVAL 1
#else
#ifdef SHORT_TEST_EPOCH
  #define TEST_EPOCH 5
  #define TIME_INTERVAL 0.2
#else
#ifdef MIDDLE_TEST_EPOCH
  #define TEST_EPOCH 10
  #define TIME_INTERVAL 1
#else
  #define TEST_EPOCH 20  // 10
  #define TIME_INTERVAL 0.5
#endif
#endif
#endif

#define MAX_THREAD_REQUEST 10000000
#define LOAD_HEARTBEAT 100000
#define USE_CORO
#define EPOCH_LAT_TEST
// #define NO_WRITE_CONFLICT  // NO_WRITE_CONFLICT only support int workloads
#define LOADER_NUM 8

extern uint64_t cache_miss[MAX_APP_THREAD];
extern uint64_t cache_hit[MAX_APP_THREAD];
extern uint64_t lock_fail[MAX_APP_THREAD];
extern uint64_t try_lock[MAX_APP_THREAD];
extern uint64_t read_retry[MAX_APP_THREAD];
extern uint64_t try_read[MAX_APP_THREAD];
extern int g_root_level;

#ifdef RM_INTERNAL_AMPLIFICATION
extern uint64_t warmup_cnts[MAX_APP_THREAD][define::kMaxCoro];
#endif

int kThreadCount;
int kNodeCount;
int kCoroCnt = 8;
bool kIsStr;
bool kIsScan;
#ifdef USE_CORO
bool kUseCoro = true;
#else
bool kUseCoro = false;
#endif

std::string ycsb_load_path;
std::string ycsb_trans_path;
int fix_range_size = -1;


std::thread th[MAX_APP_THREAD];
uint64_t tp[MAX_APP_THREAD][MAX_CORO_NUM];

extern volatile bool need_stop;
extern uint64_t latency[MAX_APP_THREAD][MAX_CORO_NUM][LATENCY_WINDOWS];
uint64_t latency_th_all[LATENCY_WINDOWS];

std::default_random_engine e;
std::uniform_int_distribution<Value> randval(kValueMin, kValueMax);

Tree *tree;
DSM *dsm;

#ifdef NO_WRITE_CONFLICT
inline Key to_key(uint64_t k) {
  return int2key((CityHash64((char *)&k, sizeof(k)) + 1));
}
#endif

class RequsetGenBench : public RequstGen {
public:
  RequsetGenBench(DSM* dsm, Request* req, int req_num, int coro_id, int coro_cnt) :
                  dsm(dsm), req(req), req_num(req_num), coro_id(coro_id), coro_cnt(coro_cnt) {
    local_thread_id = dsm->getMyThreadID();
    cur = coro_id;
    epoch_id = 0;
    extra_k = MAX_KEY_SPACE_SIZE + kThreadCount * kCoroCnt * dsm->getMyNodeID() + local_thread_id * kCoroCnt + coro_id;
    flag = false;
  }

  Request next() override {
    cur = (cur + coro_cnt) % req_num;
    if (req[cur].is_insert) {
      if (cur + coro_cnt >= req_num) {
        // need_stop = true;
        ++ epoch_id;
        flag = true;
      }
      if (kIsStr) {
        req[cur].k = req[cur].k + epoch_id;   // For insert workloads, key should remain nonexist
      }
      else if (flag) {
        req[cur].k = int2key(extra_k);
        extra_k += kThreadCount * kCoroCnt * dsm->getClusterSize();
      }
    }
    tp[local_thread_id][coro_id]++;
    req[cur].v = randval(e);  // make value different per-epoch
    return req[cur];
  }

private:
  DSM *dsm;
  Request* req;
  int req_num;
  int coro_id;
  int coro_cnt;
  int local_thread_id;
  int cur;
  uint8_t epoch_id;
  uint64_t extra_k;
  bool flag;
};


RequstGen *gen_func(DSM* dsm, Request* req, int req_num, int coro_id, int coro_cnt) {
  return new RequsetGenBench(dsm, req, req_num, coro_id, coro_cnt);
}


void work_func(Tree *tree, const Request& r, CoroContext *ctx, int coro_id) {
  if (r.is_search) {
    Value v;
    tree->search(r.k, v, ctx, coro_id);
  }
  else if (r.is_update || r.is_insert) {
    tree->insert(r.k, r.v, ctx, coro_id);
  }
  else {
    std::map<Key, Value> ret;
    tree->range_query(r.k, r.k + r.range_size, ret);
  }
}


Timer bench_timer;
std::atomic<int64_t> warmup_cnt{0};
std::atomic_bool ready{false};

void thread_load(int id) {
  // use LOADER_NUM threads to load ycsb
  uint64_t loader_id = std::min(kThreadCount, LOADER_NUM) * dsm->getMyNodeID() + id;

  printf("I am loader %lu\n", loader_id);

  // 1. insert ycsb_load
  std::string op;
  std::ifstream load_in(ycsb_load_path + std::to_string(loader_id));
  if (!load_in.is_open()) {
    printf("Error opening load file\n");
    assert(false);
  }
  Key k;
  int cnt = 0;
  if (!kIsStr) {  // int workloads
    uint64_t int_k;
    while (load_in >> op >> int_k) {
#ifdef NO_WRITE_CONFLICT
      k = to_key(int_k);
#else
      k = int2key(int_k);
#endif
      assert(op == "INSERT");
      tree->insert(k, randval(e));
      if (++ cnt % LOAD_HEARTBEAT == 0) {
        printf("thread %lu: %d load entries loaded.\n", loader_id, cnt);
      }
    }
  }
  else {  // string workloads
    std::string str_k;
    std::string line;
    while (std::getline(load_in, line)) {
      if (!line.size()) continue;
      std::istringstream tmp(line);
      tmp >> op >> str_k;
      if (str_k[0] == '\0') continue;
      k = str2key(str_k);
      assert(op == "INSERT");
      tree->insert(k, randval(e));
      if (++ cnt % LOAD_HEARTBEAT == 0) {
        printf("thread %lu: %d load entries loaded.\n", loader_id, cnt);
      }
    }
  }
  printf("loader %lu load finish\n", loader_id);
}


void thread_run(int id) {
  bindCore(id * 2 + 1);  // bind to CPUs in NUMA that close to mlx5_2

  dsm->registerThread();
  uint64_t my_id = kThreadCount * dsm->getMyNodeID() + id;

  printf("I am %lu\n", my_id);

  if (id == 0) {
    bench_timer.begin();
  }

  // 1. insert ycsb_load
  if (id < std::min(kThreadCount, LOADER_NUM)) {
    thread_load(id);
  }

  // 2. load ycsb_trans
  Request* req = new Request[MAX_THREAD_REQUEST];
  int req_num = 0;
  std::ifstream trans_in(ycsb_trans_path + std::to_string(my_id));
  if (!trans_in.is_open()) {
    printf("Error opening trans file\n");
    assert(false);
  }
  std::string op;
  int cnt = 0;
  if (!kIsStr) {  // int workloads
    int range_size = 0;
    uint64_t int_k;
    while(trans_in >> op >> int_k) {
      if (op == "SCAN") trans_in >> range_size;
      else range_size = 0;
      Request r;
      r.is_search = (op == "READ");
      r.is_insert = (op == "INSERT");
      r.is_update = (op == "UPDATE");
      r.range_size = fix_range_size >= 0 ? fix_range_size : range_size;
#ifdef NO_WRITE_CONFLICT
      // NO_WRITE_CONFLICT should use YCSB workload with insertorder=ordered and do manual hash
      if (r.is_update || r.is_insert) {
        uint64_t all_thread_num = kThreadCount * dsm->getClusterSize();
        int_k = int_k / all_thread_num * all_thread_num + my_id;
        assert(int_k % all_thread_num == my_id);
      }
      r.k = to_key(int_k);
#else
      r.k = int2key(int_k);
#endif
      req[req_num ++] = r;
      if (++ cnt % LOAD_HEARTBEAT == 0) {
        printf("thread %d: %d trans entries loaded.\n", id, cnt);
      }
    }
  }
  else {
    std::string str_k;
    std::string line;
    while (std::getline(trans_in, line)) {
      if (!line.size()) continue;
      std::istringstream tmp(line);
      tmp >> op >> str_k;
      assert(op != "SCAN");  // string workloads currently does not support SCAN
      Request r;
      r.is_search = (op == "READ");
      r.is_insert = (op == "INSERT");
      r.is_update = (op == "UPDATE");
      assert(r.is_search || r.is_insert || r.is_update);
      r.range_size = 0;
      r.k = str2key(str_k);
      req[req_num ++] = r;
      if (++ cnt % LOAD_HEARTBEAT == 0) {
        printf("thread %d: %d trans entries loaded.\n", id, cnt);
      }
    }
  }

  warmup_cnt.fetch_add(1);

  if (id == 0) {
    while (warmup_cnt.load() != kThreadCount)
      ;
    printf("node %d finish\n", dsm->getMyNodeID());
    dsm->barrier("warm_finish");

    uint64_t ns = bench_timer.end();
    printf("warmup time %lds\n", ns / 1000 / 1000 / 1000);

    ready = true;
    warmup_cnt.store(-1);
  }

  while (warmup_cnt.load() != -1)
    ;

  // 3. start ycsb test
  if (!kIsScan && kUseCoro) {
    tree->run_coroutine(gen_func, work_func, kCoroCnt, req, req_num);
  }
  else {
    /// without coro
    Timer timer;
    auto gen = new RequsetGenBench(dsm, req, req_num, 0, 0);
    auto thread_id = dsm->getMyThreadID();

    while (!need_stop) {
      auto r = gen->next();

      timer.begin();
      work_func(tree, r, nullptr, 0);
      auto us_10 = timer.end() / 100;

      if (us_10 >= LATENCY_WINDOWS) {
        us_10 = LATENCY_WINDOWS - 1;
      }
      latency[thread_id][0][us_10]++;
    }
  }
  printf("thread %d exit.\n", id);
}

void parse_args(int argc, char *argv[]) {
  if (argc != 6 && argc != 7) {
    printf("Usage: ./ycsb_test kNodeCount kThreadCount kCoroCnt workload_type[randint/email] workload_idx[a/b/c/d/e] [fix_range_size]\n");
    exit(-1);
  }

  kNodeCount = atoi(argv[1]);
  kThreadCount = atoi(argv[2]);
  kCoroCnt = atoi(argv[3]);
  kIsStr = (std::string(argv[4]) == "email");
  kIsScan = (std::string(argv[5]) == "e");
  ycsb_load_path = "../../DMB-Tree/ycsb/workloads/load_" + std::string(argv[4]) + "_workload" + std::string(argv[5]);
  ycsb_trans_path = "../../DMB-Tree/ycsb/workloads/txn_" + std::string(argv[4]) + "_workload" + std::string(argv[5]);
  if (argc == 7) fix_range_size = atoi(argv[6]);

  printf("kNodeCount %d, kThreadCount %d, kCoroCnt %d\n", kNodeCount, kThreadCount, kCoroCnt);
  printf("ycsb_load: %s\n", ycsb_load_path.c_str());
  printf("ycsb_trans: %s\n", ycsb_trans_path.c_str());
  if (argc == 7) printf("fix_range_size: %d\n", fix_range_size);
}

void save_latency(int epoch_id) {
  // sum up local latency cnt
  for (int i = 0; i < LATENCY_WINDOWS; ++i) {
    latency_th_all[i] = 0;
    for (int k = 0; k < MAX_APP_THREAD; ++k)
      for (int j = 0; j < MAX_CORO_NUM; ++j) {
        latency_th_all[i] += latency[k][j][i];
    }
  }
  // store in file
  std::ofstream f_out("../us_lat/epoch_" + std::to_string(epoch_id) + ".lat");
  f_out << std::setiosflags(std::ios::fixed) << std::setprecision(1);
  if (f_out.is_open()) {
    for (int i = 0; i < LATENCY_WINDOWS; ++i) {
      f_out << i / 10.0 << "\t" << latency_th_all[i] << std::endl;
    }
    f_out.close();
  }
  else {
    printf("Fail to write file!\n");
    assert(false);
  }
  memset(latency, 0, sizeof(uint64_t) * MAX_APP_THREAD * MAX_CORO_NUM * LATENCY_WINDOWS);
}

int main(int argc, char *argv[]) {

  parse_args(argc, argv);

  DSMConfig config;
  assert(kNodeCount >= MEMORY_NODE_NUM);
  config.machineNR = kNodeCount;
  config.threadNR = kThreadCount;
  dsm = DSM::getInstance(config);
  bindCore(kThreadCount * 2 + 1);
  dsm->registerThread();
#ifdef NEED_CACHE_EVICTION
  dsm->loadKeySpace(ycsb_load_path, kIsStr);
#endif
  tree = new Tree(dsm);

  dsm->barrier("benchmark");

  for (int i = 0; i < kThreadCount; i++) {
    th[i] = std::thread(thread_run, i);
  }


  while (!ready.load())
    ;
  timespec s, e;
  uint64_t pre_tp = 0;
  int count = 0;

  clock_gettime(CLOCK_REALTIME, &s);
  while(!need_stop) {

    sleep(TIME_INTERVAL);
    clock_gettime(CLOCK_REALTIME, &e);
    int microseconds = (e.tv_sec - s.tv_sec) * 1000000 +
                       (double)(e.tv_nsec - s.tv_nsec) / 1000;

    uint64_t all_tp = 0;
    for (int i = 0; i < MAX_APP_THREAD; ++i) {
      for (int j = 0; j < kCoroCnt; ++j)
        all_tp += tp[i][j];
    }
    clock_gettime(CLOCK_REALTIME, &s);

    uint64_t cap = all_tp - pre_tp;
    pre_tp = all_tp;

    uint64_t all = 0, hit = 0;
    for (int i = 0; i < MAX_APP_THREAD; ++i) {
      all += (cache_hit[i] + cache_miss[i]);
      hit += cache_hit[i];
    }

    uint64_t try_lock_cnt = 0, lock_fail_cnt = 0;
    for (int i = 0; i < MAX_APP_THREAD; ++i) {
      lock_fail_cnt += lock_fail[i];
      try_lock_cnt += try_lock[i];
    }

    tree->clear_debug_info();

#ifdef EPOCH_LAT_TEST
    save_latency(++ count);
#else
    if (++ count == TEST_EPOCH / 2) {  // rm latency during warm up
      memset(latency, 0, sizeof(uint64_t) * MAX_APP_THREAD * MAX_CORO_NUM * LATENCY_WINDOWS);
    }
#endif

    double per_node_tp = cap * 1.0 / microseconds;
    uint64_t cluster_tp = dsm->sum((uint64_t)(per_node_tp * 1000));   // only node 0 return the sum

    printf("%d, throughput %.4f\n", dsm->getMyNodeID(), per_node_tp);

    if (dsm->getMyNodeID() == 0) {
      printf("epoch %d passed!\n", count);
      printf("cluster throughput %.3f Mops\n", cluster_tp / 1000.0);
      printf("cache hit rate: %lf\n", hit * 1.0 / all);
      printf("avg. lock/cas fail cnt: %lf\n", lock_fail_cnt * 1.0 / try_lock_cnt);
      printf("tree height: %d\n", g_root_level);
      printf("\n");
    }
#ifdef RM_INTERNAL_AMPLIFICATION
    // uint64_t sum = 0;
    // bool is_ok = false;
    // for (int i = 0; !is_ok && i < MAX_APP_THREAD; ++ i) {
    //   for (int j = 0; !is_ok && j < define::kMaxCoro; ++ j) {
    //     sum += warmup_cnts[i][j];
    //     printf("epoch=%d warmup cnts=%lu\n", count, sum);
    //   }
    // }
    if (count == 19) {
      assert(warmup_cnts[0][0] > 100000);
    }
#endif
    if (count >= TEST_EPOCH) {
      need_stop = true;
    }
  }
#ifndef EPOCH_LAT_TEST
  save_latency(1);
#endif
  printf("[END]\n");
  for (int i = 0; i < kThreadCount; i++) {
    th[i].join();
    printf("Thread %d joined.\n", i);
  }
  tree->statistics();
  dsm->barrier("fin");

  return 0;
}
