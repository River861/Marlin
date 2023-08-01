#if !defined(_INDEX_CACHE_H_)
#define _INDEX_CACHE_H_

#include "CacheEntry.h"
#include "HugePageAlloc.h"
#include "Timer.h"
#include "third_party/inlineskiplist.h"
#include "DSM.h"

#include <tbb/concurrent_queue.h>
#include <queue>
#include <atomic>
#include <vector>

extern bool enter_debug;

using CacheSkipList = InlineSkipList<CacheEntryComparator>;

class IndexCache {

public:
  IndexCache(int cache_size, DSM* dsm);

  bool add_to_cache(InternalPage *page);
  const CacheEntry *search_from_cache(const Key &k, GlobalAddress *addr, bool& next_is_leaf,
                                      bool is_leader = false);

  void search_range_from_cache(const Key &from, const Key &to,
                               std::vector<InternalPage> &result);

  bool add_entry(const Key &from, const Key &to, InternalPage *ptr);
  const CacheEntry *find_entry(const Key &k);
  const CacheEntry *find_entry(const Key &from, const Key &to);

  bool invalidate(const CacheEntry *entry);

  const CacheEntry *get_a_random_entry(uint64_t &freq);

  void statistics();

  void bench();

  bool is_full();

private:
  uint64_t cache_size; // MB;
  std::atomic<int64_t> free_page_cnt;
  std::atomic<int64_t> skiplist_node_cnt;
  int64_t all_page_cnt;

  std::queue<std::pair<void *, uint64_t> > delay_free_list;
  WRLock free_lock;

  // SkipList
  CacheSkipList *skiplist;
  CacheEntryComparator cmp;
  Allocator alloc;

  // Eviction
  DSM *dsm;
  // tbb::concurrent_queue<const CacheEntry *> eviction_list;

  void evict_one();
  void evict();
};

inline IndexCache::IndexCache(int cache_size, DSM* dsm) : cache_size(cache_size), dsm(dsm) {
  skiplist = new CacheSkipList(cmp, &alloc, 21);
  uint64_t memory_size = define::MB * cache_size;

  all_page_cnt = memory_size / sizeof(InternalPage);
  free_page_cnt.store(all_page_cnt);
  skiplist_node_cnt.store(0);
}

inline bool IndexCache::is_full() {
  return free_page_cnt.load() == 0;
}

// [from, to）
inline bool IndexCache::add_entry(const Key &from, const Key &to,
                                  InternalPage *ptr) {

  // TODO memory leak
  auto buf = skiplist->AllocateKey(sizeof(CacheEntry));
  auto &e = *(CacheEntry *)buf;
  e.from = from;
  e.to = to - 1; // !IMPORTANT;
  e.ptr = ptr;

  auto res = skiplist->InsertConcurrently(buf);
  // if (res) {
  //   eviction_list.push((const CacheEntry *)buf);
  // }
  return res;
}

inline const CacheEntry *IndexCache::find_entry(const Key &from,
                                                const Key &to) {
  CacheSkipList::Iterator iter(skiplist);

  CacheEntry e;
  e.from = from;
  e.to = to - 1;
  iter.Seek((char *)&e);
  if (iter.Valid()) {
    auto val = (const CacheEntry *)iter.key();
    return val;
  } else {
    return nullptr;
  }
}

inline const CacheEntry *IndexCache::find_entry(const Key &k) {
  return find_entry(k, k + 1);
}

inline bool IndexCache::add_to_cache(InternalPage *page) {
  // assert(page->hdr.level == 1);
  auto new_page = (InternalPage *)malloc(kInternalPageSize);
  memcpy(new_page, page, kInternalPageSize);
  new_page->index_cache_freq = 0;

  if (this->add_entry(page->hdr.lowest, page->hdr.highest, new_page)) {
    skiplist_node_cnt.fetch_add(1);
    auto v = free_page_cnt.fetch_add(-1);
    if (v <= 0) {
      evict();
    }
    return true;
  } else { // conflicted
    auto e = this->find_entry(page->hdr.lowest, page->hdr.highest);
    if (e && e->from == page->hdr.lowest && e->to == page->hdr.highest - 1) {
      auto ptr = e->ptr;
      auto ret_val = __sync_val_compare_and_swap(&(e->ptr), ptr, new_page);
      if (ret_val == ptr) { /// cas_success
        if (ret_val == nullptr) {
          auto v = free_page_cnt.fetch_add(-1);
          if (v < 0) {
            evict();
          }
        }
        // eviction_list.push(e);
        return true;
      }
    }
    free(new_page);
    return false;
  }
}

inline const CacheEntry *IndexCache::search_from_cache(const Key &k,
                                                       GlobalAddress *addr, bool& next_is_leaf, bool is_leader) {
  if (is_leader && !delay_free_list.empty()) { // try to free a page in the delay-free-list
    auto p = delay_free_list.front();
    if (asm_rdtsc() - p.second > 3000ull * 10) {
      free(p.first);
      free_page_cnt.fetch_add(1);

      free_lock.wLock();
      delay_free_list.pop();
      free_lock.wUnlock();
    }
  }

  auto entry = find_entry(k);

  InternalPage *page = entry ? entry->ptr : nullptr;

  if (page && entry->from <= k && entry->to >= k) {


    page->index_cache_freq++;
    next_is_leaf = page->hdr.level == 1;

    auto cnt = page->hdr.last_index + 1;
    if (k < page->records[0].key) {
      *addr = page->hdr.leftmost_ptr;
    } else {

      bool find = false;
      for (int i = 1; i < cnt; ++i) {
        if (k < page->records[i].key) {
          find = true;
          *addr = page->records[i - 1].ptr;
          break;
        }
      }
      if (!find) {
        *addr = page->records[cnt - 1].ptr;
      }
    }

    compiler_barrier();
    if (entry->ptr) { // check if it is freed.
      // printf("Cache HIt\n");
      return entry;
    }
  }

  return nullptr;
}

inline void
IndexCache::search_range_from_cache(const Key &from, const Key &to,
                                    std::vector<InternalPage> &result) {
  CacheSkipList::Iterator iter(skiplist);

  result.clear();
  CacheEntry e;
  e.from = from;
  e.to = from;
  iter.Seek((char *)&e);

  while (iter.Valid()) {
    auto val = (const CacheEntry *)iter.key();
    if (val->ptr) {
      if (val->from > to) {
        return;
      }
      result.push_back(*(val->ptr));
    }
    iter.Next();
  }
}

inline bool IndexCache::invalidate(const CacheEntry *entry) {
  auto ptr = entry->ptr;

  if (ptr == nullptr) {
    return false;
  }

  if (__sync_bool_compare_and_swap(&(entry->ptr), ptr, 0)) {
    // free(ptr);
    free_lock.wLock();
    delay_free_list.push(std::make_pair(ptr, asm_rdtsc()));
    free_page_cnt.fetch_add(1);
    free_lock.wUnlock();
    return true;
  }

  return false;
}

inline const CacheEntry *IndexCache::get_a_random_entry(uint64_t &freq) {  // TODO: email workload eviction
  // CacheSkipList::Iterator iter(skiplist);
  // uint32_t seed = asm_rdtsc();
  // GlobalAddress tmp_addr;
retry:
  // auto e = this->search_from_cache(k, &tmp_addr);
  auto e = this->find_entry(dsm->getRandomKey());

  if (!e) {
    goto retry;
  }
  auto ptr = e->ptr;
  if (!ptr) {
    goto retry;
  }

  freq = ptr->index_cache_freq;
  if (e->ptr != ptr) {
    goto retry;
  }
  return e;
}

inline void IndexCache::evict_one() {

  uint64_t freq1, freq2;
  auto e1 = get_a_random_entry(freq1);
  auto e2 = get_a_random_entry(freq2);

  if (freq1 < freq2) {
    invalidate(e1);
  } else {
    invalidate(e2);
  }
}

inline void IndexCache::evict() {  // FIFO
  // do {
  //   const CacheEntry* next;
  //   if(eviction_list.try_pop(next)) {
  //     invalidate(next);
  //   }
  // } while (free_page_cnt.load() < 0 && !eviction_list.empty());
  do {
    evict_one();
  } while (free_page_cnt.load() < 0);
}

inline void IndexCache::statistics() {
  // printf("[skiplist node: %ld]  [page cache: %ld]\n", skiplist_node_cnt.load(),
  //        all_page_cnt - free_page_cnt.load());
  uint64_t occupy_size = cache_size * define::MB - free_page_cnt * sizeof(InternalPage);
  std::cout << " ----- [IndexCache]: " << " cache size=" << cache_size << " MB"
                                       << " all_entry_cnt=" << all_page_cnt
                                       << " free_entry_cnt=" << free_page_cnt
                                       << " free_size=" << free_page_cnt * sizeof(InternalPage) / define::MB << " MB"
                                       << " skiplist_node_cnt=" << skiplist_node_cnt << " ----- " << std::endl;
  std::cout << "comsumed cache size=" << (double)cache_size - (double)free_page_cnt * sizeof(InternalPage) / define::MB << " MB" << std::endl;
  std::map<int, int64_t> cnt;
  CacheSkipList::Iterator iter(skiplist);
  iter.SeekToFirst();
  uint64_t kp_cnt = 0;
  uint64_t index_overhead = skiplist->GetHeightSum() * 8;
  std::cout << "skiplist pointer num=" << skiplist->GetHeightSum() << std::endl;
  while(iter.Valid()) {
    index_overhead += sizeof(CacheEntry);
    auto e = (const CacheEntry *)iter.key();
    auto context = e->ptr;
    if (context) {
      auto level = context->hdr.level;
      if (cnt.find(level) == cnt.end()) cnt[level] = 0;
      cnt[level] ++;
      kp_cnt += context->hdr.last_index;
    }
    iter.Next();
  }
  for (const auto& e : cnt) {
    std::cout << "level=" << e.first << " cnt=" << e.second << std::endl;
  }
  occupy_size += index_overhead;
  std::cout << "cache kp efficiency=" << (double)occupy_size / kp_cnt << " B" << std::endl;
  std::cout << "leaf span=" << kLeafCardinality << std::endl;
  std::cout << "cache efficiency=" << (double)occupy_size / kp_cnt / kLeafCardinality << " B" << std::endl;
}

inline void IndexCache::bench() {

  Timer t;
  t.begin();
  const int loop = 100000;

  for (int i = 0; i < loop; ++i) {
    uint64_t r = rand() % (5 * define::MB);
    this->find_entry(int2key(r));
  }

  t.end_print(loop);
}

#endif // _INDEX_CACHE_H_
