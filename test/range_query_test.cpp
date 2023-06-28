#include "Timer.h"
#include "Tree.h"
#include "zipf.h"

#include <city.h>
#include <stdlib.h>
#include <thread>
#include <time.h>
#include <unistd.h>
#include <vector>
#include <mutex>
std::mutex mutex;

// #define USE_CORO

extern uint64_t cache_miss[MAX_APP_THREAD];
extern uint64_t cache_hit[MAX_APP_THREAD];

int kReadRatio;
int kThreadCount;
int kNodeCount;
uint64_t kKeySpace = 8 * define::MB;
double kWarmRatio = 0.8;

double zipfan = 0.99;
int kCoroCnt = 8;
int kRangeSize = 100;

std::thread th[MAX_APP_THREAD];
uint64_t tp[MAX_APP_THREAD][MAX_CORO_NUM];

extern volatile bool need_stop;
extern uint64_t latency[MAX_APP_THREAD][MAX_CORO_NUM][LATENCY_WINDOWS];
uint64_t latency_th_all[LATENCY_WINDOWS];

Tree *tree;
DSM *dsm;


inline Key to_key(uint64_t k) {
  return int2key((CityHash64((char *)&k, sizeof(k)) + 1) % kKeySpace);
}


class RequsetGenBench : public RequstGen {

public:
  RequsetGenBench(DSM *dsm, int coro_id): id(dsm->getMyThreadID()), coro_id(coro_id) {
    seed = rdtsc();
    mehcached_zipf_init(&state, kKeySpace, zipfan,
                        (rdtsc() & (0x0000ffffffffffffull)) ^ id);
  }

  Request next() override {
    Request r;
    uint64_t dis = mehcached_zipf_next(&state);

    r.k = to_key(dis);
    r.v = ++ val;
    r.is_search = rand_r(&seed) % 100 < kReadRatio;

    tp[id][coro_id]++;
    return r;
  }

private:
  int id;
  int coro_id;
  uint64_t val = 0;
  unsigned int seed;
  struct zipf_gen_state state;
};


RequstGen *gen_func(DSM* dsm, Request* req, int req_num, int coro_id, int coro_cnt) {
  return new RequsetGenBench(dsm, coro_id);
}


void work_func(Tree *tree, const Request& r, CoroContext *ctx, int coro_id) {
  thread_local std::map<Key, Value> all_ret[MAX_CORO_NUM];
  auto& ret = all_ret[coro_id];
  ret.clear();
  tree->range_query(r.k, r.k + kRangeSize, ret);
}


Timer bench_timer;
std::atomic<int64_t> warmup_cnt{0};
std::atomic_bool ready{false};


void thread_run(int id) {

  bindCore(id * 2 + 1);  // bind to CPUs in NUMA that close to mlx5_2

  dsm->registerThread();

  uint64_t all_thread = kThreadCount * dsm->getClusterSize();
  uint64_t my_id = kThreadCount * dsm->getMyNodeID() + id;

  printf("I am %lu\n", my_id);

  if (id == 0) {
    bench_timer.begin();
  }

  uint64_t end_warm_key = kWarmRatio * kKeySpace;
  for (uint64_t i = 1; i < end_warm_key; ++i) {
    if (i % all_thread == my_id) {
      mutex.lock();  // safely insert
      tree->insert(to_key(i), i * 2);
      mutex.unlock();
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
    warmup_cnt.store(0);
  }

  while (warmup_cnt.load() != 0)
    ;


#ifdef USE_CORO
  tree->run_coroutine(gen_func, work_func, kCoroCnt, nullptr, 0);
#else
  /// without coro
  Timer timer;
  auto gen = new RequsetGenBench(dsm, 0);
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
#endif

  printf("thread %d exit.\n", id);
}

void parse_args(int argc, char *argv[]) {
  if (argc != 6) {
    printf("Usage: ./range_query_test kNodeCount kRangeSize kThreadCount zipfan kCoroCnt\n");
    exit(-1);
  }

  kNodeCount = atoi(argv[1]);
  kRangeSize = atoi(argv[2]);
  kThreadCount = atoi(argv[3]);
  zipfan = atof(argv[4]);
  kCoroCnt = atoi(argv[5]);
  kReadRatio = 100;

  printf("kNodeCount %d, kRangeSize %d, kThreadCount %d, zipfan %lf, kCoroCnt %d\n", kNodeCount, kRangeSize,
          kThreadCount, zipfan, kCoroCnt);
}

void cal_latency() {
  uint64_t all_lat = 0;
  for (int i = 0; i < LATENCY_WINDOWS; ++i) {
    latency_th_all[i] = 0;
    for (int k = 0; k < MAX_APP_THREAD; ++k)
      for (int j = 0; j < MAX_CORO_NUM; ++j) {
        latency_th_all[i] += latency[k][j][i];
    }
    all_lat += latency_th_all[i];
  }
  memset(latency, 0, sizeof(uint64_t) * MAX_APP_THREAD * MAX_CORO_NUM * LATENCY_WINDOWS);

  uint64_t th50 = all_lat / 2;
  uint64_t th90 = all_lat * 9 / 10;
  uint64_t th95 = all_lat * 95 / 100;
  uint64_t th99 = all_lat * 99 / 100;
  uint64_t th999 = all_lat * 999 / 1000;

  uint64_t cum = 0;
  for (int i = 0; i < LATENCY_WINDOWS; ++i) {
    cum += latency_th_all[i];

    if (cum >= th50) {
      printf("p50 %f\t", i / 10.0);
      th50 = -1;
    }
    if (cum >= th90) {
      printf("p90 %f\t", i / 10.0);
      th90 = -1;
    }
    if (cum >= th95) {
      printf("p95 %f\t", i / 10.0);
      th95 = -1;
    }
    if (cum >= th99) {
      printf("p99 %f\t", i / 10.0);
      th99 = -1;
    }
    if (cum >= th999) {
      printf("p999 %f\n", i / 10.0);
      th999 = -1;
      return;
    }
  }
}

int main(int argc, char *argv[]) {

  parse_args(argc, argv);

  DSMConfig config;
  config.machineNR = kNodeCount;
  config.threadNR = kThreadCount;
  dsm = DSM::getInstance(config);
  dsm->registerThread();
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
  int epoch = 8;
  while(!need_stop) {

    sleep(2);
    clock_gettime(CLOCK_REALTIME, &e);
    int microseconds = (e.tv_sec - s.tv_sec) * 1000000 +
                       (double)(e.tv_nsec - s.tv_nsec) / 1000;

    uint64_t all_tp = 0;
    for (int i = 0; i < MAX_APP_THREAD; ++i) {
      for (int j = 0; j < kCoroCnt; ++ j)
        all_tp += tp[i][j];
    }
    uint64_t cap = all_tp - pre_tp;
    pre_tp = all_tp;

    uint64_t all = 0;
    uint64_t hit = 0;
    for (int i = 0; i < MAX_APP_THREAD; ++i) {
      all += (cache_hit[i] + cache_miss[i]);
      hit += cache_hit[i];
    }

    if (epoch-- <= 0) {
      need_stop = true;
    }

    clock_gettime(CLOCK_REALTIME, &s);

    if (++count % 3 == 0 && dsm->getMyNodeID() == 1) {
      cal_latency();
    }

    double per_node_tp = cap * 1.0 / microseconds;
    uint64_t cluster_tp = dsm->sum((uint64_t)(per_node_tp * 1000));

    printf("%d, throughput %.4f\n", dsm->getMyNodeID(), per_node_tp);

    if (dsm->getMyNodeID() == 0) {
      printf("cluster throughput %.3f\n", cluster_tp / 1000.0);
      printf("cache hit rate: %lf\n", hit * 1.0 / all);
    }
    tree->clear_debug_info();
  }
  for (int i = 0; i < kThreadCount; i++) {
    th[i].join();
    printf("Thread %d joined.\n", i);
  }
  tree->statistics();
  dsm->barrier("fin");

  return 0;
}
