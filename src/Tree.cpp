#include "Tree.h"
#include "IndexCache.h"
#include "RdmaBuffer.h"
#include "Timer.h"

#include <algorithm>
#include <city.h>
#include <iostream>
#include <queue>
#include <utility>
#include <vector>
#include <map>
// #include <mutex>

// std::mutex cout_lock;
bool enter_debug = false;

uint64_t cache_miss[MAX_APP_THREAD];
uint64_t cache_hit[MAX_APP_THREAD];
uint64_t lock_fail[MAX_APP_THREAD];
uint64_t try_lock[MAX_APP_THREAD];
uint64_t read_retry[MAX_APP_THREAD];
uint64_t try_read[MAX_APP_THREAD];
uint64_t pattern[MAX_APP_THREAD][8];
uint64_t hierarchy_lock[MAX_APP_THREAD][8];
uint64_t handover_count[MAX_APP_THREAD][8];
uint64_t hot_filter_count[MAX_APP_THREAD][8];
uint64_t latency[MAX_APP_THREAD][MAX_CORO_NUM][LATENCY_WINDOWS];
volatile bool need_stop = false;

thread_local CoroCall Tree::worker[define::kMaxCoro];
thread_local CoroCall Tree::master;
thread_local GlobalAddress path_stack[define::kMaxCoro]
                                     [define::kMaxLevelOfTree];

// for coroutine schedule
struct CoroDeadline {
  uint64_t deadline;
  uint16_t coro_id;

  bool operator<(const CoroDeadline &o) const {
    return this->deadline < o.deadline;
  }
};

thread_local Timer timer;
thread_local CoroQueue busy_waiting_queue;
thread_local std::priority_queue<CoroDeadline> deadline_queue;

Tree::Tree(DSM *dsm, uint16_t tree_id) : dsm(dsm), tree_id(tree_id) {

  for (int i = 0; i < dsm->getClusterSize(); ++i) {
    local_locks[i] = new HOCLNode[define::kNumOfLock];
    for (size_t k = 0; k < define::kNumOfLock; ++k) {
      auto &n = local_locks[i][k];
      n.ticket_lock.store(0);
      n.hand_over = false;
      n.hand_time = 0;
    }
  }

  assert(dsm->is_register());
  print_verbose();

  index_cache = new IndexCache(define::kIndexCacheSize, dsm);

  local_lock_table = new LocalLockTable();
  root_ptr_ptr = get_root_ptr_ptr();

  // try to init tree and install root pointer
  auto page_buffer = (dsm->get_rbuf(0)).get_page_buffer();
  auto root_addr = dsm->alloc(kLeafPageSize);
  auto root_page = new (page_buffer) LeafPage;

  root_page->set_consistent();
  dsm->write_sync(page_buffer, root_addr, kLeafPageSize);

  auto cas_buffer = (dsm->get_rbuf(0)).get_cas_buffer();
  bool res = dsm->cas_sync(root_ptr_ptr, 0, root_addr.val, cas_buffer);
  if (res) {
    std::cout << "Tree root pointer value " << root_addr << std::endl;
  } else {
    // std::cout << "fail\n";
  }
}

void Tree::print_verbose() {

  int kLeafHdrOffset = STRUCT_OFFSET(LeafPage, hdr);
  int kInternalHdrOffset = STRUCT_OFFSET(InternalPage, hdr);
  assert(kLeafHdrOffset == kInternalHdrOffset);

  if (dsm->getMyNodeID() == 0) {
    std::cout << "Header size: " << sizeof(Header) << std::endl;
    std::cout << "Internal Page size: " << sizeof(InternalPage) << " ["
              << kInternalPageSize << "]" << std::endl;
    std::cout << "Internal per Page: " << kInternalCardinality << std::endl;
    std::cout << "Leaf Page size: " << sizeof(LeafPage) << " [" << kLeafPageSize
              << "]" << std::endl;
    std::cout << "Leaf per Page: " << kLeafCardinality << std::endl;
    std::cout << "LeafEntry size: " << sizeof(LeafEntry) << std::endl;
    std::cout << "InternalEntry size: " << sizeof(InternalEntry) << std::endl;
  }
}

inline void Tree::before_operation(CoroContext *cxt, int coro_id) {
  for (size_t i = 0; i < define::kMaxLevelOfTree; ++i) {
    path_stack[coro_id][i] = GlobalAddress::Null();
  }
}

GlobalAddress Tree::get_root_ptr_ptr() {
  GlobalAddress addr;
  addr.nodeID = 0;
  addr.offset =
      define::kRootPointerStoreOffest + sizeof(GlobalAddress) * tree_id;

  return addr;
}

extern GlobalAddress g_root_ptr;
extern int g_root_level;
extern bool enable_cache;
GlobalAddress Tree::get_root_ptr(CoroContext *cxt, int coro_id) {

  if (g_root_ptr == GlobalAddress::Null()) {
    auto page_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
    dsm->read_sync(page_buffer, root_ptr_ptr, sizeof(GlobalAddress), cxt);
    GlobalAddress root_ptr = *(GlobalAddress *)page_buffer;
    return root_ptr;
  } else {
    return g_root_ptr;
  }

  // std::cout << "root ptr " << root_ptr << std::endl;
}

void Tree::broadcast_new_root(GlobalAddress new_root_addr, int root_level) {
  RawMessage m;
  m.type = RpcType::NEW_ROOT;
  m.addr = new_root_addr;
  m.level = root_level;
  for (int i = 0; i < dsm->getClusterSize(); ++i) {
    dsm->rpc_call_dir(m, i);
  }
}

bool Tree::update_new_root(GlobalAddress left, const Key &k,
                           GlobalAddress right, int level,
                           GlobalAddress old_root, CoroContext *cxt,
                           int coro_id) {

  auto page_buffer = dsm->get_rbuf(coro_id).get_page_buffer();
  auto cas_buffer = dsm->get_rbuf(coro_id).get_cas_buffer();
  auto new_root = new (page_buffer) InternalPage(left, k, right, level);

  auto new_root_addr = dsm->alloc(kInternalPageSize);

  new_root->set_consistent();
  dsm->write_sync(page_buffer, new_root_addr, kInternalPageSize, cxt);
  if (dsm->cas_sync(root_ptr_ptr, old_root.to_uint64(), new_root_addr.to_uint64(), cas_buffer, cxt)) {
    broadcast_new_root(new_root_addr, level);
    std::cout << "new root level " << level << " " << new_root_addr
              << std::endl;
    return true;
  } else {
    std::cout << "cas root fail " << std::endl;
  }

  return false;
}

void Tree::print_and_check_tree(CoroContext *cxt, int coro_id) {
  assert(dsm->is_register());

  auto root = get_root_ptr(cxt, coro_id);
  // SearchResult result;

  GlobalAddress p = root;
  GlobalAddress levels[define::kMaxLevelOfTree];
  int level_cnt = 0;
  auto page_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
  GlobalAddress leaf_head;

next_level:

  dsm->read_sync(page_buffer, p, kLeafPageSize);
  auto header = (Header *)(page_buffer + (STRUCT_OFFSET(LeafPage, hdr)));
  levels[level_cnt++] = p;
  if (header->level != 0) {
    p = header->leftmost_ptr;
    goto next_level;
  } else {
    leaf_head = p;
  }

next:
  dsm->read_sync(page_buffer, leaf_head, kLeafPageSize);
  auto page = (LeafPage *)page_buffer;
  for (int i = 0; i < kLeafCardinality; ++i) {
    if (page->records[i].value != kValueNull) {
    }
  }
  while (page->hdr.sibling_ptr != GlobalAddress::Null()) {
    leaf_head = page->hdr.sibling_ptr;
    goto next;
  }

  // for (int i = 0; i < level_cnt; ++i) {
  //   dsm->read_sync(page_buffer, levels[i], kLeafPageSize);
  //   auto header = (Header *)(page_buffer + (STRUCT_OFFSET(LeafPage, hdr)));
  //   // std::cout << "addr: " << levels[i] << " ";
  //   // header->debug();
  //   // std::cout << " | ";
  //   while (header->sibling_ptr != GlobalAddress::Null()) {
  //     dsm->read_sync(page_buffer, header->sibling_ptr, kLeafPageSize);
  //     header = (Header *)(page_buffer + (STRUCT_OFFSET(LeafPage, hdr)));
  //     // std::cout << "addr: " << header->sibling_ptr << " ";
  //     // header->debug();
  //     // std::cout << " | ";
  //   }
  //   // std::cout << "\n------------------------------------" << std::endl;
  //   // std::cout << "------------------------------------" << std::endl;
  // }
}

inline bool Tree::try_lock_addr(GlobalAddress lock_addr, uint64_t tag,
                                uint64_t *buf, CoroContext *cxt, int coro_id) {
  auto &pattern_cnt = pattern[dsm->getMyThreadID()][lock_addr.nodeID];

  bool hand_over = acquire_local_lock(lock_addr, cxt, coro_id);
  if (hand_over) {
    return true;
  }

  {
    uint64_t retry_cnt = 0;
    uint64_t pre_tag = 0;
    uint64_t conflict_tag = 0;
    try_lock[dsm->getMyThreadID()]++;
retry:
    retry_cnt++;
    if (retry_cnt > 1000000) {
      std::cout << "Deadlock " << lock_addr << std::endl;

      std::cout << dsm->getMyNodeID() << ", " << dsm->getMyThreadID()
                << " locked by " << (conflict_tag >> 32) << ", "
                << (conflict_tag << 32 >> 32) << std::endl;
      assert(false);
    }

#ifdef CONFIG_ENABLE_EMBEDDING_LOCK
    bool res = dsm->cas_sync(lock_addr, 0, tag, buf, cxt);
#else
    bool res = dsm->cas_dm_sync(lock_addr, 0, tag, buf, cxt);
#endif

    pattern_cnt++;
    if (!res) {
      conflict_tag = *buf - 1;
      if (conflict_tag != pre_tag) {
        retry_cnt = 0;
        pre_tag = conflict_tag;
      }
      lock_fail[dsm->getMyThreadID()]++;
      goto retry;
    }
  }

  return true;
}

inline void Tree::unlock_addr(GlobalAddress lock_addr, uint64_t tag,
                              uint64_t *buf, CoroContext *cxt, int coro_id,
                              bool async) {

  bool hand_over_other = can_hand_over(lock_addr);
  if (hand_over_other) {
    releases_local_lock(lock_addr);
    return;
  }

  auto cas_buf = dsm->get_rbuf(coro_id).get_cas_buffer();

  *cas_buf = 0;
#ifdef CONFIG_ENABLE_EMBEDDING_LOCK
  if (async) {
    dsm->write((char *)cas_buf, lock_addr, sizeof(uint64_t), false);
  } else {
    dsm->write_sync((char *)cas_buf, lock_addr, sizeof(uint64_t), cxt);
  }
#else
  if (async) {
    dsm->write_dm((char *)cas_buf, lock_addr, sizeof(uint64_t), false);
  } else {
    dsm->write_dm_sync((char *)cas_buf, lock_addr, sizeof(uint64_t), cxt);
  }
#endif

  releases_local_lock(lock_addr);
}

inline bool Tree::try_spear_addr(GlobalAddress lock_addr, bool is_SMO,
                                 uint64_t *buf, CoroContext *cxt, int coro_id, bool from_IDU) {
  bool hand_over = acquire_local_lock(lock_addr, cxt, coro_id);
  if (hand_over) {
    return true;
  }

  try_lock[dsm->getMyThreadID()]++;
  int64_t SMO_delta = from_IDU ? -SMO_X-1 : -SMO_X;
#ifdef CONFIG_ENABLE_EMBEDDING_LOCK
  dsm->faa_boundary_sync(lock_addr, is_SMO ? SMO_delta : 1, buf, 63ULL, cxt);
#else
  dsm->faa_dm_boundary_sync(lock_addr, is_SMO ? SMO_delta : 1, buf, 63ULL, cxt);
#endif
  auto ret = *(int64_t *)buf;
  if (is_SMO) {
    if (ret == 0) return true;
  }
  else {
    if (ret >= 0) return true;
  }

  {
retry:
    lock_fail[dsm->getMyThreadID()]++;
#ifdef CONFIG_ENABLE_EMBEDDING_LOCK
    dsm->read_sync(buf, lock_addr, sizeof(uint64_t), cxt);
#else
    dsm->read_dm_sync(buf, lock_addr, sizeof(uint64_t), cxt);
#endif
    auto ret = *(int64_t *)buf;
    if (is_SMO) {
      if (ret != -SMO_X) goto retry;
    }
    else {
      if (ret < 0) goto retry;
    }
  }
  return true;
}

inline void Tree::unspear_addr(GlobalAddress lock_addr, bool is_SMO, uint64_t *buf,
                    CoroContext *cxt, int coro_id, bool async) {
  bool hand_over_other = can_hand_over(lock_addr);
  if (hand_over_other) {
    releases_local_lock(lock_addr);
    return;
  }

  auto buf = dsm->get_rbuf(coro_id).get_cas_buffer();

#ifdef CONFIG_ENABLE_EMBEDDING_LOCK
  if (async) {
    dsm->faa_boundary(lock_addr, is_SMO ? SMO_X : -1, buf, 63ULL, false, cxt);
  } else {
    dsm->faa_boundary_sync(lock_addr, is_SMO ? SMO_X : -1, buf, 63ULL, cxt);
  }
#else
  if (async) {
    dsm->faa_dm_boundary(lock_addr, is_SMO ? SMO_X : -1, buf, 63ULL, false, cxt);
  } else {
    dsm->faa_dm_boundary_sync(lock_addr, is_SMO ? SMO_X : -1, buf, 63ULL, cxt);
  }
#endif

  releases_local_lock(lock_addr);
}

void Tree::write_page_and_unlock(char *page_buffer, GlobalAddress page_addr,
                                 int page_size, uint64_t *cas_buffer,
                                 GlobalAddress lock_addr, uint64_t tag,
                                 CoroContext *cxt, int coro_id, bool async) {
  bool hand_over_other = can_hand_over(lock_addr);
  if (hand_over_other) {
    dsm->write_sync(page_buffer, page_addr, page_size, cxt);
    releases_local_lock(lock_addr);
    return;
  }

  RdmaOpRegion rs[2];
  rs[0].source = (uint64_t)page_buffer;
  rs[0].dest = page_addr.to_uint64();
  rs[0].size = page_size;
  rs[0].is_on_chip = false;

  auto cas_buf = dsm->get_rbuf(coro_id).get_cas_buffer();
  *cas_buf = 0;
  rs[1].source = (uint64_t)cas_buf;
  rs[1].dest = lock_addr.to_uint64();
  rs[1].size = sizeof(uint64_t);
#ifdef CONFIG_ENABLE_EMBEDDING_LOCK
  rs[1].is_on_chip = false;
#else
  rs[1].is_on_chip = true;
#endif

  if (async) {
    dsm->write_batch(rs, 2, false);
  } else {
    dsm->write_batch_sync(rs, 2, cxt);
  }

  releases_local_lock(lock_addr);
}

void Tree::write_page_and_unspear(char *page_buffer, GlobalAddress page_addr,
                                  int page_size, uint64_t *cas_buffer,
                                  GlobalAddress lock_addr, bool is_SMO,
                                  CoroContext *cxt, int coro_id, bool async) {
  bool hand_over_other = can_hand_over(lock_addr);
  if (hand_over_other) {
    dsm->write_sync(page_buffer, page_addr, page_size, cxt);
    releases_local_lock(lock_addr);
    return;
  }

  RdmaOpRegion rs[2];
  rs[0].source = (uint64_t)page_buffer;
  rs[0].dest = page_addr.to_uint64();
  rs[0].size = page_size;
  rs[0].is_on_chip = false;

  auto buf = dsm->get_rbuf(coro_id).get_cas_buffer();
  rs[1].source = (uint64_t)buf;
  rs[1].dest = lock_addr.to_uint64();
  rs[1].size = sizeof(uint64_t);
#ifdef CONFIG_ENABLE_EMBEDDING_LOCK
  rs[1].is_on_chip = false;
#else
  rs[1].is_on_chip = true;
#endif

  if (async) {
    dsm->write_faa(rs[0], rs[1], is_SMO ? SMO_X : -1, false, cxt);
  } else {
    dsm->write_faa_sync(rs[0], rs[1], is_SMO ? SMO_X : -1, cxt);
  }

  releases_local_lock(lock_addr);
}

void Tree::lock_and_read_page(char *page_buffer, GlobalAddress page_addr,
                              int page_size, uint64_t *cas_buffer,
                              GlobalAddress lock_addr, uint64_t tag,
                              CoroContext *cxt, int coro_id) {
  try_lock_addr(lock_addr, tag, cas_buffer, cxt, coro_id);

  dsm->read_sync(page_buffer, page_addr, page_size, cxt);
  pattern[dsm->getMyThreadID()][page_addr.nodeID]++;
}

void Tree::spear_and_read_page(char *page_buffer, GlobalAddress page_addr,
                               int page_size, uint64_t *cas_buffer,
                               GlobalAddress lock_addr, bool is_SMO,
                               CoroContext *cxt, int coro_id) {
  try_spear_addr(lock_addr, is_SMO, cas_buffer, cxt, coro_id);

  dsm->read_sync(page_buffer, page_addr, page_size, cxt);
  pattern[dsm->getMyThreadID()][page_addr.nodeID]++;
}

void Tree::lock_bench(const Key &k, CoroContext *cxt, int coro_id) {
  uint64_t lock_index = CityHash64((char *)&k, sizeof(k)) % define::kNumOfLock;

  GlobalAddress lock_addr;
  lock_addr.nodeID = 0;
  lock_addr.offset = lock_index * sizeof(uint64_t);
  auto cas_buffer = dsm->get_rbuf(coro_id).get_cas_buffer();

  // bool res = dsm->cas_sync(lock_addr, 0, 1, cas_buffer, cxt);
  try_lock_addr(lock_addr, 1, cas_buffer, cxt, coro_id);
  unlock_addr(lock_addr, 1, cas_buffer, cxt, coro_id, true);
}

void Tree::insert_internal(const Key &k, GlobalAddress v, CoroContext *cxt,
                           int coro_id, int level) {
  auto root = get_root_ptr(cxt, coro_id);
  SearchResult result;

  GlobalAddress p = root;

  try_read[dsm->getMyThreadID()] ++;
next:

  if (!page_search(p, k, result, cxt, coro_id) || result.level == 0) {
    // std::cout << "SEARCH WARNING insert" << std::endl;
    p = get_root_ptr(cxt, coro_id);
    // sleep(1);
    goto next;
  }

  assert(result.level != 0);
  if (result.slibing != GlobalAddress::Null()) {
    p = result.slibing;
    goto next;
  }

  p = result.next_level;
  if (result.level != level + 1) {
    goto next;
  }

  internal_page_store(p, k, v, root, level, cxt, coro_id);
}


void Tree::insert(const Key &k, const Value &v, CoroContext *cxt, int coro_id) {
  assert(dsm->is_register());

  before_operation(cxt, coro_id);

  // handover
  bool write_handover = false;
  std::pair<bool, bool> lock_res = std::make_pair(false, false);

#ifdef TREE_ENABLE_WRITE_COMBINING
  lock_res = local_lock_table->acquire_local_write_lock(k, v, &busy_waiting_queue, cxt);
  write_handover = (lock_res.first && !lock_res.second);
#else
  UNUSED(lock_res);
#endif
  if (write_handover) {
    goto insert_finish;
  }

  {
  if (enable_cache) {
    GlobalAddress cache_addr;
    auto entry = index_cache->search_from_cache(k, &cache_addr);
    if (entry) { // cache hit
      auto root = get_root_ptr(cxt, coro_id);
      if (leaf_page_store(cache_addr, k, v, root, 0, cxt, coro_id, true)) {
        cache_hit[dsm->getMyThreadID()]++;
        goto insert_finish;
      }
      // cache stale, from root,
      index_cache->invalidate(entry);
    }
    cache_miss[dsm->getMyThreadID()]++;
  }

  auto root = get_root_ptr(cxt, coro_id);
  SearchResult result;

  GlobalAddress p = root;
  try_read[dsm->getMyThreadID()] ++;

next:
  if (!page_search(p, k, result, cxt, coro_id)) {
    // std::cout << "SEARCH WARNING insert" << std::endl;
    p = get_root_ptr(cxt, coro_id);
    // sleep(1);
    goto next;
  }

  if (!result.is_leaf) {
    assert(result.level != 0);
    if (result.slibing != GlobalAddress::Null()) {
      p = result.slibing;
      goto next;
    }

    p = result.next_level;
    if (result.level != 1) {  // 不是倒数第二层
      goto next;
    }
  }

  leaf_page_store(p, k, v, root, 0, cxt, coro_id, false);
  }

insert_finish:
#ifdef TREE_ENABLE_WRITE_COMBINING
  local_lock_table->release_local_write_lock(k, lock_res);
#endif
  return;
}


bool Tree::search(const Key &k, Value &v, CoroContext *cxt, int coro_id) {
  assert(dsm->is_register());

  // handover
  bool search_res = false;
  std::pair<bool, bool> lock_res = std::make_pair(false, false);
  bool read_handover = false;

#ifdef TREE_ENABLE_READ_DELEGATION
  lock_res = local_lock_table->acquire_local_read_lock(k, &busy_waiting_queue, cxt);
  read_handover = (lock_res.first && !lock_res.second);
#else
  UNUSED(lock_res);
#endif
  if (read_handover) {
    goto search_finish;
  }

  {
  auto root = get_root_ptr(cxt, coro_id);
  SearchResult result;

  GlobalAddress p = root;

  bool from_cache = false;
  const CacheEntry *entry = nullptr;
  if (enable_cache) {
    GlobalAddress cache_addr;
    entry = index_cache->search_from_cache(k, &cache_addr);
    if (entry) { // cache hit
      cache_hit[dsm->getMyThreadID()]++;
      from_cache = true;
      p = cache_addr;
    } else {
      cache_miss[dsm->getMyThreadID()]++;
    }
  }
  try_read[dsm->getMyThreadID()] ++;

next:
  if (!page_search(p, k, result, cxt, coro_id, from_cache)) {
    if (from_cache) { // cache stale
      index_cache->invalidate(entry);
      cache_hit[dsm->getMyThreadID()]--;
      cache_miss[dsm->getMyThreadID()]++;
      from_cache = false;

      p = root;
    } else {
      // std::cout << "SEARCH WARNING search" << std::endl;
      // sleep(1);
    }
    goto next;
  }
  if (result.is_leaf) {
    if (result.val != kValueNull) { // find
      v = result.val;
      search_res = true;
    }
    else if (result.slibing != GlobalAddress::Null()) { // turn right
      p = result.slibing;
      goto next;
    }
#ifdef ENABLE_VAR_SIZE_KV
    if (search_res) {
      // read the DataBlock
      auto block_len = ((DataPointer *)&v)->data_len;
      auto block_addr = ((DataPointer *)&v)->ptr;
      auto block_buffer = (dsm->get_rbuf(coro_id)).get_block_buffer();
      dsm->read_sync(block_buffer, (GlobalAddress)block_addr, block_len, cxt);
      v = ((DataBlock*)block_buffer)->value;
    }
#endif
    goto search_finish; // not found
  } else {        // internal
    p = result.slibing != GlobalAddress::Null() ? result.slibing
                                                : result.next_level;
    goto next;
  }
  }

search_finish:
#ifdef TREE_ENABLE_READ_DELEGATION
  local_lock_table->release_local_read_lock(k, lock_res, search_res, v);  // handover the ret leaf addr
#endif
  return search_res;
}

bool Tree::level_one_page_search(const Key &k, TmpResult* t_res, CoroContext *cxt, int coro_id) {
  auto root = get_root_ptr(cxt, coro_id);

  GlobalAddress p = root;
  SearchResult result;
  try_read[dsm->getMyThreadID()] ++;

next:
  t_res->is_leaf = false;
  t_res->level = 0;
  if (!page_search(p, k, result, cxt, coro_id, false, t_res)) {
    return false;
  }
  if (result.slibing != GlobalAddress::Null()) {
    p = result.slibing;
    goto next;
  }
  if (result.level <= 1) {
    return true;
  }
  else {  // internal
    p = result.next_level;
    goto next;
  }
}


uint64_t Tree::range_query(const Key &from, const Key &to, std::map<Key, Value> &ret,
                           CoroContext *cxt, int coro_id) {

  const int kParaFetch = 32;
  thread_local std::vector<InternalPage> result;
  thread_local std::vector<GlobalAddress> leaves;

  result.clear();
  leaves.clear();
  index_cache->search_range_from_cache(from, to, result);

  // FIXME: here, we assume all innernal nodes are cached in compute node
  if (result.empty()) {
    for(auto k = from; k < to; k = k + spanSize) search(k, ret[k], cxt, coro_id);  // load into cache
    printf("loading cache...");
    return 0;
  }

  uint64_t counter = 0;
  for (auto page : result) {
    auto cnt = page.hdr.last_index + 1;
    auto addr = page.hdr.leftmost_ptr;

    // [from, to]
    // [lowest, page.records[0].key);
    bool no_fetch = from > page.records[0].key || to < page.hdr.lowest;
    if (!no_fetch) {
      leaves.push_back(addr);
    }
    for (int i = 1; i < cnt; ++i) {
      no_fetch = from > page.records[i].key || to < page.records[i - 1].key;
      if (!no_fetch) {
        leaves.push_back(page.records[i - 1].ptr);
      }
    }

    no_fetch = from > page.hdr.highest || to < page.records[cnt - 1].key;
    if (!no_fetch) {
      leaves.push_back(page.records[cnt - 1].ptr);
    }
  }

  int cq_cnt = 0;
  char *range_buffer = (dsm->get_rbuf(coro_id)).get_range_buffer();
  for (size_t i = 0; i < leaves.size(); ++i) {
    if (i > 0 && i % kParaFetch == 0) {
      dsm->poll_rdma_cq(kParaFetch);
      cq_cnt -= kParaFetch;
      for (int k = 0; k < kParaFetch; ++k) {
        auto page = (LeafPage *)(range_buffer + k * kLeafPageSize);
        for (int i = 0; i < kLeafCardinality; ++i) {
          auto &r = page->records[i];
          if (r.value != kValueNull) {
#ifndef TREE_ENABLE_MARLIN
            if (r.f_version != r.r_version) continue;
#endif
            if (r.key >= from && r.key <= to) {
              ret[r.key] = r.value;
            }
          }
        }
      }
    }
    dsm->read(range_buffer + kLeafPageSize * (i % kParaFetch), leaves[i],
              kLeafPageSize, true);
    cq_cnt++;
  }

  if (cq_cnt != 0) {
    dsm->poll_rdma_cq(cq_cnt);
    for (int k = 0; k < cq_cnt; ++k) {
      auto page = (LeafPage *)(range_buffer + k * kLeafPageSize);
      for (int i = 0; i < kLeafCardinality; ++i) {
        auto &r = page->records[i];
        if (r.value != kValueNull) {
#ifndef TREE_ENABLE_MARLIN
          if (r.f_version != r.r_version) continue;
#endif
          if (r.key >= from && r.key <= to) {
            ret[r.key] = r.value;
          }
        }
      }
    }
  }

  for(auto k = from; k < to; k = k + 1) {
    if (ret.find(k) != ret.end()) {
      cache_hit[dsm->getMyThreadID()]++;
    }
    else {
      cache_miss[dsm->getMyThreadID()]++;
      search(k, ret[k], cxt, coro_id);
    }
  }

#ifdef ENABLE_VAR_SIZE_KV
  // read DataBlocks via doorbell batching
  std::map<Key, Value> indirect_values;
  std::vector<RdmaOpRegion> kv_rs;
  int kv_cnt = 0;
  for (const auto& [_, data_ptr] : ret) {
    auto data_addr = ((DataPointer*)&data_ptr)->ptr;
    auto data_len  = ((DataPointer*)&data_ptr)->data_len;
    RdmaOpRegion r;
    r.source     = (uint64_t)range_buffer + kv_cnt * define::dataBlockLen;
    r.dest       = ((GlobalAddress)data_addr).to_uint64();
    r.size       = data_len;
    r.is_on_chip = false;
    kv_rs.push_back(r);
    kv_cnt ++;
  }
  dsm->read_batches_sync(kv_rs);
  kv_cnt = 0;
  for (auto& [_, v] : ret) {
    auto data_block = (DataBlock*)(range_buffer + kv_cnt * define::dataBlockLen);
    v = data_block->value;
    kv_cnt ++;
  }
#endif
  return counter;
}

// Del needs to be rewritten
void Tree::del(const Key &k, CoroContext *cxt, int coro_id) {
  assert(dsm->is_register());
  before_operation(cxt, coro_id);

  auto root = get_root_ptr(cxt, coro_id);
  SearchResult result;

  GlobalAddress p = root;
  try_read[dsm->getMyThreadID()] ++;

next:
  if (!page_search(p, k, result, cxt, coro_id)) {
    std::cout << "SEARCH WARNING" << std::endl;
    goto next;
  }

  if (!result.is_leaf) {
    assert(result.level != 0);
    if (result.slibing != GlobalAddress::Null()) {
      p = result.slibing;
      goto next;
    }

    p = result.next_level;
    if (result.level != 1) {

      goto next;
    }
  }

  leaf_page_del(p, k, 0, cxt, coro_id);
}

bool Tree::page_search(GlobalAddress page_addr, const Key &k,
                       SearchResult &result, CoroContext *cxt, int coro_id,
                       bool from_cache, TmpResult* t_res) {
  auto page_buffer = (dsm->get_rbuf(coro_id)).get_page_buffer();
  assert(STRUCT_OFFSET(LeafPage, hdr) == STRUCT_OFFSET(InternalPage, hdr));
  auto header = (Header *)(page_buffer + (STRUCT_OFFSET(LeafPage, hdr)));
  auto &pattern_cnt = pattern[dsm->getMyThreadID()][page_addr.nodeID];

  int counter = 0;
re_read:
  read_retry[dsm->getMyThreadID()] ++;
  if (++counter > 100) {
    printf("re read too many times\n");
    sleep(1);
  }
  dsm->read_sync(page_buffer, page_addr, std::max(kLeafPageSize, kInternalPageSize), cxt);
  pattern_cnt++;

  memset(&result, 0, sizeof(result));
  result.is_leaf = header->leftmost_ptr == GlobalAddress::Null();
  result.level = header->level;
  path_stack[coro_id][result.level] = page_addr;

  if (result.is_leaf) {
    auto page = (LeafPage *)page_buffer;
    if (!page->check_consistent()) {
      goto re_read;
    }
    // if(t_res) {
    //   t_res->is_leaf = true;
    //   t_res->tmp_leaf = *page;
    // }

    if (from_cache &&
        (k < page->hdr.lowest || k >= page->hdr.highest)) { // cache is stale
      return false;
    }

    // assert(result.level == 0);  // BUG
    if (result.level != 0) {
      return false;
    }
    if (k >= page->hdr.highest) { // should turn right
      result.slibing = page->hdr.sibling_ptr;
      return true;
    }
    if (k < page->hdr.lowest) {
      // assert(false);
      return false;
    }
    leaf_page_search(page, k, result);
  } else {
    auto page = (InternalPage *)page_buffer;
    if (!page->check_consistent()) {
      goto re_read;
    }
    if (result.level == 0) return false;
    assert(!from_cache);

    if(t_res && result.level) {
      t_res->level = result.level;
      t_res->tmp_page = *page;
    }

    if (result.level == 1 && enable_cache) {
      index_cache->add_to_cache(page);  // 存放倒数第二层的到cache中
      // if (enter_debug) {
      //   printf("add %lud [%lud %lud]\n", k, page->hdr.lowest,
      //          page->hdr.highest);
      // }
    }

    if (k >= page->hdr.highest) { // should turn right
      result.slibing = page->hdr.sibling_ptr;
      return true;
    }
    if (k < page->hdr.lowest) {
      // printf("key %ld error in level %d\n", k, page->hdr.level);
      // sleep(10);
      // print_and_check_tree();
      // assert(false);
      return false;
    }
    internal_page_search(page, k, result);
  }

  return true;
}

void Tree::internal_page_search(InternalPage *page, const Key &k,
                                SearchResult &result) {

  assert(k >= page->hdr.lowest);
  if (k >= page->hdr.highest) { // should turn right  // BUG: 很可能是这里导致的cache启动失败
    result.slibing = page->hdr.sibling_ptr;
    return;
  }
  assert(k < page->hdr.highest);

  auto cnt = page->hdr.last_index + 1;
  // page->debug();
  if (k < page->records[0].key) {
    result.next_level = page->hdr.leftmost_ptr;
    return;
  }

  for (int i = 1; i < cnt; ++i) {
    if (k < page->records[i].key) {
      result.next_level = page->records[i - 1].ptr;
      return;
    }
  }
  result.next_level = page->records[cnt - 1].ptr;
}

void Tree::leaf_page_search(LeafPage *page, const Key &k,
                            SearchResult &result) {

  for (int i = 0; i < kLeafCardinality; ++i) {
    auto &r = page->records[i];
    if (r.key == k && r.value != kValueNull) {
#ifndef TREE_ENABLE_MARLIN
      if (r.f_version != r.r_version) continue;
#endif
      result.val = r.value;
      break;
    }
  }
}

void Tree::internal_page_store(GlobalAddress page_addr, const Key &k,
                               GlobalAddress v, GlobalAddress root, int level,
                               CoroContext *cxt, int coro_id) {
  uint64_t lock_index =
      CityHash64((char *)&page_addr, sizeof(page_addr)) % define::kNumOfLock;

  GlobalAddress lock_addr;

#ifdef CONFIG_ENABLE_EMBEDDING_LOCK
  lock_addr = page_addr;
#else
  lock_addr.nodeID = page_addr.nodeID;
  lock_addr.offset = lock_index * sizeof(uint64_t);
#endif

  auto &rbuf = dsm->get_rbuf(coro_id);
  uint64_t *cas_buffer = rbuf.get_cas_buffer();
  auto page_buffer = rbuf.get_page_buffer();

  auto tag = dsm->getThreadTag();
  assert(tag != 0);

  lock_and_read_page(page_buffer, page_addr, kInternalPageSize, cas_buffer,
                     lock_addr, tag, cxt, coro_id);

  auto page = (InternalPage *)page_buffer;

  assert(page->hdr.level == level);
  assert(page->check_consistent());
  if (k >= page->hdr.highest) {

    this->unlock_addr(lock_addr, tag, cas_buffer, cxt, coro_id, true);

    assert(page->hdr.sibling_ptr != GlobalAddress::Null());

    this->internal_page_store(page->hdr.sibling_ptr, k, v, root, level, cxt,
                              coro_id);

    return;
  }
  assert(k >= page->hdr.lowest);

  auto cnt = page->hdr.last_index + 1;

  bool is_update = false;
  uint16_t insert_index = 0;
  for (int i = cnt - 1; i >= 0; --i) {
    if (page->records[i].key == k) { // find and update
      page->records[i].ptr = v;
      // assert(false);
      is_update = true;
      break;
    }
    if (page->records[i].key < k) {
      insert_index = i + 1;
      break;
    }
  }

  assert(cnt != kInternalCardinality);

  if (!is_update) { // insert and shift
    for (int i = cnt; i > insert_index; --i) {
      page->records[i].key = page->records[i - 1].key;
      page->records[i].ptr = page->records[i - 1].ptr;
    }
    page->records[insert_index].key = k;
    page->records[insert_index].ptr = v;

    page->hdr.last_index++;
  }

  cnt = page->hdr.last_index + 1;
  bool need_split = cnt == kInternalCardinality;
  Key split_key;
  GlobalAddress sibling_addr;
  if (need_split) { // need split
    sibling_addr = dsm->alloc(kInternalPageSize);
    auto sibling_buf = rbuf.get_sibling_buffer();

    auto sibling = new (sibling_buf) InternalPage(page->hdr.level);

    //    std::cout << "addr " <<  sibling_addr << " | level " <<
    //    (int)(page->hdr.level) << std::endl;

    int m = cnt / 2;
    split_key = page->records[m].key;
    assert(split_key > page->hdr.lowest);
    assert(split_key < page->hdr.highest);
    for (int i = m + 1; i < cnt; ++i) { // move
      sibling->records[i - m - 1].key = page->records[i].key;
      sibling->records[i - m - 1].ptr = page->records[i].ptr;
    }
    page->hdr.last_index -= (cnt - m);
    sibling->hdr.last_index += (cnt - m - 1);

    sibling->hdr.leftmost_ptr = page->records[m].ptr;
    sibling->hdr.lowest = page->records[m].key;
    sibling->hdr.highest = page->hdr.highest;
    page->hdr.highest = page->records[m].key;

    // link
    sibling->hdr.sibling_ptr = page->hdr.sibling_ptr;
    page->hdr.sibling_ptr = sibling_addr;

    sibling->set_consistent();
    dsm->write_sync(sibling_buf, sibling_addr, kInternalPageSize, cxt);
  }

  page->set_consistent();
  write_page_and_unlock(page_buffer, page_addr, kInternalPageSize, cas_buffer,
                        lock_addr, tag, cxt, coro_id, need_split);

  if (!need_split)
    return;

  if (root == page_addr) { // update root

    if (update_new_root(page_addr, split_key, sibling_addr, level + 1, root,
                        cxt, coro_id)) {
      return;
    }
    else {
      insert_internal(split_key, sibling_addr, cxt, coro_id, level + 1);
      return;
    }
  }

  auto up_level = path_stack[coro_id][level + 1];

  if (up_level != GlobalAddress::Null()) {
    internal_page_store(up_level, split_key, sibling_addr, root, level + 1, cxt,
                        coro_id);
  } else {
    assert(false);
  }
}

bool Tree::leaf_page_store(GlobalAddress page_addr, const Key &k,
                           Value v, GlobalAddress root, int level,
                           CoroContext *cxt, int coro_id, bool from_cache) {

  uint64_t lock_index =
      CityHash64((char *)&page_addr, sizeof(page_addr)) % define::kNumOfLock;

  GlobalAddress lock_addr;

#ifdef CONFIG_ENABLE_EMBEDDING_LOCK
  lock_addr = page_addr;
#else
  lock_addr.nodeID = page_addr.nodeID;
  lock_addr.offset = lock_index * sizeof(uint64_t);
#endif

  auto &rbuf = dsm->get_rbuf(coro_id);
  uint64_t *cas_buffer = rbuf.get_cas_buffer();
  auto page_buffer = rbuf.get_page_buffer();

  auto tag = dsm->getThreadTag();
  assert(tag != 0);

#ifdef TREE_ENABLE_MARLIN
  spear_and_read_page(page_buffer, page_addr, kLeafPageSize, cas_buffer,
                     lock_addr, false, cxt, coro_id);
#else
  lock_and_read_page(page_buffer, page_addr, kLeafPageSize, cas_buffer,
                     lock_addr, tag, cxt, coro_id);
#endif

  auto page = (LeafPage *)page_buffer;

  assert(page->hdr.level == level);
  assert(page->check_consistent());

  if (from_cache &&
      (k < page->hdr.lowest || k >= page->hdr.highest)) { // cache is stale
#ifdef TREE_ENABLE_MARLIN
    unspear_addr(lock_addr, false, cas_buffer, cxt, coro_id, true);
#else
    unlock_addr(lock_addr, tag, cas_buffer, cxt, coro_id, true);
#endif
    return false;
  }

  if (k >= page->hdr.highest) {
#ifdef TREE_ENABLE_MARLIN
    unspear_addr(lock_addr, false, cas_buffer, cxt, coro_id, true);
#else
    unlock_addr(lock_addr, tag, cas_buffer, cxt, coro_id, true);
#endif
    assert(page->hdr.sibling_ptr != GlobalAddress::Null());
    leaf_page_store(page->hdr.sibling_ptr, k, v, root, level, cxt,
                    coro_id, false);
    return true;
  }
  assert(k >= page->hdr.lowest);

#ifdef TREE_ENABLE_WRITE_COMBINING
  local_lock_table->get_combining_value(k, v);
#endif


#ifdef ENABLE_VAR_SIZE_KV
  {
  // first write a new DataBlock out-of-place
  auto block_buffer = (dsm->get_rbuf(coro_id)).get_block_buffer();
  auto data_block = new (block_buffer) DataBlock(v);
  auto block_addr = dsm->alloc(define::dataBlockLen);
  dsm->write_sync(block_buffer, block_addr, define::dataBlockLen, cxt);
  // change value into the DataPointer value pointing to the DataBlock
  v = (uint64_t)DataPointer(define::dataBlockLen, block_addr);
  }
#endif

  int cnt = 0;
  int empty_index = -1;
  char *update_pos = nullptr;
  Value old_v = kValueNull;
  for (int i = 0; i < kLeafCardinality; ++i) {
    auto &r = page->records[i];
    if (r.value != kValueNull) {
      cnt++;
      if (r.key == k) {
        old_v = r.value;
        r.value = v;
#ifndef TREE_ENABLE_MARLIN
        r.f_version ++;
        r.r_version = r.f_version;
#endif
        update_pos = (char *)&r;
        break;
      }
    } else if (empty_index == -1) {
      empty_index = i;
    }
  }

  assert(cnt != kLeafCardinality);

  bool is_insert = false;
  if (update_pos == nullptr) { // insert new item
    is_insert = true;
    if (empty_index == -1) {
      printf("%d cnt\n", cnt);
      assert(false);
    }
    auto &r = page->records[empty_index];
    r.key = k;
    r.value = v;
#ifndef TREE_ENABLE_MARLIN
    r.f_version++;
    r.r_version = r.f_version;
#endif
    update_pos = (char *)&r;
    cnt++;
  }

  bool need_split = cnt == kLeafCardinality;
  if (!need_split) {
    assert(update_pos);
#ifdef TREE_ENABLE_MARLIN
    // modify value_pointer with CAS
    auto key_addr = page_addr + (update_pos - (char *)page);
    auto ptr_addr = key_addr + define::keyLen;
    auto cas_buf = dsm->get_rbuf(coro_id).get_cas_buffer();
cas_retry:
    if (!dsm->cas_sync(ptr_addr, old_v, v, cas_buf, cxt)) {
      old_v = *(Value *)cas_buf;
      goto cas_retry;
    }
    if (is_insert) { // write key and unlock
      write_page_and_unspear(update_pos, key_addr, define::keyLen, cas_buf, lock_addr, false, cxt, coro_id, false);
    }
    else {  // unlock
      unspear_addr(lock_addr, false, cas_buf, cxt, coro_id, false);
    }
#else
    UNUSED(old_v);
    UNUSED(is_insert);
    write_page_and_unlock(
        update_pos, page_addr + (update_pos - (char *)page),
        sizeof(LeafEntry), cas_buffer, lock_addr, tag, cxt, coro_id, false);
#endif
    return true;
  }

  assert(need_split);
  std::sort(
      page->records, page->records + kLeafCardinality,
      [](const LeafEntry &a, const LeafEntry &b) { return a.key < b.key; });

  Key split_key;
  GlobalAddress sibling_addr;

  sibling_addr = dsm->alloc(kLeafPageSize);
  auto sibling_buf = rbuf.get_sibling_buffer();

  auto sibling = new (sibling_buf) LeafPage(page->hdr.level);

  int m = cnt / 2;
  split_key = page->records[m].key;
  assert(split_key > page->hdr.lowest);
  assert(split_key < page->hdr.highest);

  for (int i = m; i < cnt; ++i) { // move
    sibling->records[i - m].key = page->records[i].key;
    sibling->records[i - m].value = page->records[i].value;
    // page->records[i].key = 0;
    std::fill(page->records[i].key.begin(), page->records[i].key.end(), 0);
    page->records[i].value = kValueNull;
  }
  page->hdr.last_index -= (cnt - m);
  sibling->hdr.last_index += (cnt - m);

  sibling->hdr.lowest = split_key;
  sibling->hdr.highest = page->hdr.highest;
  page->hdr.highest = split_key;

  // link
  sibling->hdr.sibling_ptr = page->hdr.sibling_ptr;
  page->hdr.sibling_ptr = sibling_addr;

  sibling->set_consistent();
  dsm->write_sync(sibling_buf, sibling_addr, kLeafPageSize, cxt);

  page->set_consistent();

#ifdef TREE_ENABLE_MARLIN
  try_spear_addr(lock_addr, true, cas_buffer, cxt, coro_id, true);
  write_page_and_unspear(page_buffer, page_addr, kLeafPageSize, cas_buffer, lock_addr, true, cxt, coro_id, true);
#else
  write_page_and_unlock(page_buffer, page_addr, kLeafPageSize, cas_buffer, lock_addr, tag, cxt, coro_id, true);
#endif

  if (root == page_addr) { // update root
    if (update_new_root(page_addr, split_key, sibling_addr, level + 1, root,
                        cxt, coro_id)) {
      return true;
    }
    else {
      insert_internal(split_key, sibling_addr, cxt, coro_id, level + 1);
      return true;
    }
  }

  auto up_level = path_stack[coro_id][level + 1];

  if (up_level != GlobalAddress::Null()) {
    internal_page_store(up_level, split_key, sibling_addr, root, level + 1, cxt,
                        coro_id);
  } else {
    // assert(from_cache);
    insert_internal(split_key, sibling_addr, cxt, coro_id, level + 1);
  }

  return true;
}

// Need BIG FIX
void Tree::leaf_page_del(GlobalAddress page_addr, const Key &k, int level,
                         CoroContext *cxt, int coro_id) {
  uint64_t lock_index =
      CityHash64((char *)&page_addr, sizeof(page_addr)) % define::kNumOfLock;

  GlobalAddress lock_addr;

#ifdef CONFIG_ENABLE_EMBEDDING_LOCK
  lock_addr = page_addr;
#else
  lock_addr.nodeID = page_addr.nodeID;
  lock_addr.offset = lock_index * sizeof(uint64_t);
#endif

  uint64_t *cas_buffer = dsm->get_rbuf(coro_id).get_cas_buffer();

  auto tag = dsm->getThreadTag();
  try_lock_addr(lock_addr, tag, cas_buffer, cxt, coro_id);

  auto page_buffer = dsm->get_rbuf(coro_id).get_page_buffer();
  dsm->read_sync(page_buffer, page_addr, kLeafPageSize, cxt);
  auto page = (LeafPage *)page_buffer;

  assert(page->hdr.level == level);
  assert(page->check_consistent());
  if (k >= page->hdr.highest) {
    this->unlock_addr(lock_addr, tag, cas_buffer, cxt, coro_id, true);

    assert(page->hdr.sibling_ptr != GlobalAddress::Null());

    this->leaf_page_del(page->hdr.sibling_ptr, k, level, cxt, coro_id);
  }

  auto cnt = page->hdr.last_index + 1;

  int del_index = -1;
  for (int i = 0; i < cnt; ++i) {
    if (page->records[i].key == k) { // find and update
      del_index = i;
      break;
    }
  }

  if (del_index != -1) { // remove and shift
    for (int i = del_index + 1; i < cnt; ++i) {
      page->records[i - 1].key = page->records[i].key;
      page->records[i - 1].value = page->records[i].value;
    }

    page->hdr.last_index--;

    page->set_consistent();
    dsm->write_sync(page_buffer, page_addr, kLeafPageSize, cxt);
  }
  this->unlock_addr(lock_addr, tag, cas_buffer, cxt, coro_id, false);
}

void Tree::run_coroutine(GenFunc gen_func, WorkFunc work_func, int coro_cnt, Request* req, int req_num) {
  using namespace std::placeholders;

  assert(coro_cnt <= MAX_CORO_NUM);
  for (int i = 0; i < coro_cnt; ++i) {
    RequstGen *gen = gen_func(dsm, req, req_num, i, coro_cnt);
    worker[i] = CoroCall(std::bind(&Tree::coro_worker, this, _1, gen, work_func, i));
  }

  master = CoroCall(std::bind(&Tree::coro_master, this, _1, coro_cnt));

  master();
}


void Tree::coro_worker(CoroYield &yield, RequstGen *gen, WorkFunc work_func, int coro_id) {
  CoroContext ctx;
  ctx.coro_id = coro_id;
  ctx.master = &master;
  ctx.yield = &yield;

  Timer coro_timer;
  auto thread_id = dsm->getMyThreadID();

  while (!need_stop) {

    auto r = gen->next();

    coro_timer.begin();
    work_func(this, r, &ctx, coro_id);
    auto us_10 = coro_timer.end() / 100;

    if (us_10 >= LATENCY_WINDOWS) {
      us_10 = LATENCY_WINDOWS - 1;
    }
    latency[thread_id][coro_id][us_10]++;
  }
}

void Tree::coro_master(CoroYield &yield, int coro_cnt) {

  for (int i = 0; i < coro_cnt; ++i) {
    yield(worker[i]);
  }

  while (!need_stop) {

    uint64_t next_coro_id;

    if (dsm->poll_rdma_cq_once(next_coro_id)) {
      yield(worker[next_coro_id]);
    }

    if (!busy_waiting_queue.empty()) {
      next_coro_id = busy_waiting_queue.front();
      busy_waiting_queue.pop();
      yield(worker[next_coro_id]);
    }

    if (!deadline_queue.empty()) {
      auto now = timer.get_time_ns();
      auto task = deadline_queue.top();
      if (now > task.deadline) {
        deadline_queue.pop();
        yield(worker[task.coro_id]);
      }
    }
  }
}

// Local Locks
inline bool Tree::acquire_local_lock(GlobalAddress lock_addr, CoroContext *cxt,
                                     int coro_id) {
#ifdef CONFIG_ENABLE_LOCK_HANDOVER
  auto &node = local_locks[lock_addr.nodeID][lock_addr.offset / 8];
  bool is_local_locked = false;

  uint64_t lock_val = node.ticket_lock.fetch_add(1);  // 通过取值来依次排队, faa返回旧值

  uint32_t ticket = lock_val << 32 >> 32;
  uint32_t current = lock_val >> 32;

  // printf("%ud %ud\n", ticket, current);
  while (ticket != current) { // lock failed
    is_local_locked = true;

    if (cxt != nullptr) {
      busy_waiting_queue.push(coro_id);
      (*cxt->yield)(*cxt->master);
    }

    current = node.ticket_lock.load(std::memory_order_relaxed) >> 32;
  }

  if (is_local_locked) {
    hierarchy_lock[dsm->getMyThreadID()][0]++;
  }

  node.hand_time++;

  return node.hand_over;
#else
  return false;
#endif
}

inline bool Tree::can_hand_over(GlobalAddress lock_addr) {
#ifdef CONFIG_ENABLE_LOCK_HANDOVER
  auto &node = local_locks[lock_addr.nodeID][lock_addr.offset / 8];
  uint64_t lock_val = node.ticket_lock.load(std::memory_order_relaxed);

  uint32_t ticket = lock_val << 32 >> 32;
  uint32_t current = lock_val >> 32;

  if (ticket <= current + 1) { // no pending locks
    node.hand_over = false;
  } else {
    node.hand_over = node.hand_time < define::kMaxHandOverTime;
  }
  if (!node.hand_over) {
    node.hand_time = 0;
  } else {
    handover_count[dsm->getMyThreadID()][0]++;
  }

  return node.hand_over;
#else
  return false;
#endif
}

inline void Tree::releases_local_lock(GlobalAddress lock_addr) {
#ifdef CONFIG_ENABLE_LOCK_HANDOVER
  auto &node = local_locks[lock_addr.nodeID][lock_addr.offset / 8];

  node.ticket_lock.fetch_add((1ull << 32));
#endif
}

void Tree::statistics() {
#ifdef TREE_ENABLE_CACHE
  index_cache->statistics();
#endif
  // index_cache->bench();
}

void Tree::clear_debug_info() {
  memset(cache_miss, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(cache_hit, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(lock_fail, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(try_lock, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(read_retry, 0, sizeof(uint64_t) * MAX_APP_THREAD);
  memset(try_read, 0, sizeof(uint64_t) * MAX_APP_THREAD);
}
