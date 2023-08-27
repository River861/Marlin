#ifndef __COMMON_H__
#define __COMMON_H__

#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <cstring>

#include <atomic>
#include <bitset>
#include <limits>
#include <string>

#include "Debug.h"
#include "HugePageAlloc.h"
#include "Rdma.h"

#include "WRLock.h"

// CONFIG_ENABLE_EMBEDDING_LOCK and CONFIG_ENABLE_CRC
// **cannot** be ON at the same time

// #define CONFIG_ENABLE_EMBEDDING_LOCK
// #define CONFIG_ENABLE_CRC

// #define TREE_ENABLE_CACHE
// #define CONFIG_ENABLE_LOCK_HANDOVER

#define LATENCY_WINDOWS 100000
#define ALLOC_ALLIGN_BIT 8

#define STRUCT_OFFSET(type, field)                                             \
  (char *)&((type *)(0))->field - (char *)((type *)(0))

#define MAX_MACHINE 20
#define MEMORY_NODE_NUM 1
#define CPU_PHYSICAL_CORE_NUM 72  // [CONFIG]
#define MAX_KEY_SPACE_SIZE 60000000
// #define KEY_SPACE_LIMIT

#define ADD_ROUND(x, n) ((x) = ((x) + 1) % (n))

#define ROUND_UP(x, n) (((x) + (1<<(n)) - 1) & ~((1<<(n)) - 1))

#define MESSAGE_SIZE 96 // byte

#define POST_RECV_PER_RC_QP 4096

#define RAW_RECV_CQ_COUNT 4096

// #define STATIC_ID_FROM_IP

// { app thread
#define MAX_APP_THREAD 130    // 65 one additional thread for data statistics(main thread)  [CONFIG]

#define APP_MESSAGE_NR 96

#define MAX_CORO_NUM 8

// }

// { dir thread
#define NR_DIRECTORY 1

#define DIR_MESSAGE_NR 128
// }

void bindCore(uint16_t core);
char *getIP();
char *getMac();

inline int bits_in(std::uint64_t u) {
  auto bs = std::bitset<64>(u);
  return bs.count();
}

#define BOOST_COROUTINES_NO_DEPRECATION_WARNING
#include <boost/coroutine/all.hpp>

using CoroYield = boost::coroutines::symmetric_coroutine<void>::yield_type;
using CoroCall = boost::coroutines::symmetric_coroutine<void>::call_type;

struct CoroContext {
  CoroYield *yield;
  CoroCall *master;
  int coro_id;
};

namespace define {

constexpr uint64_t MB = 1024ull * 1024;
constexpr uint64_t GB = 1024ull * MB;
constexpr uint16_t kCacheLineSize = 64;

// for remote allocate
constexpr uint64_t dsmSize    = 8;        // GB  [CONFIG] 64
constexpr uint64_t kChunkSize = 16 * MB;

// for store root pointer
constexpr uint64_t kRootPointerStoreOffest = kChunkSize / 2;
static_assert(kRootPointerStoreOffest % sizeof(uint64_t) == 0, "XX");

// lock on-chip memory
constexpr uint64_t kLockStartAddr = 0;
constexpr uint64_t kLockChipMemSize = ON_CHIP_SIZE * 1024;

// number of locks
// we do not use 16-bit locks, since 64-bit locks can provide enough concurrency.
// if you wan to use 16-bit locks, call *cas_dm_mask*
constexpr uint64_t kNumOfLock = kLockChipMemSize / sizeof(uint64_t);

// level of tree
constexpr uint64_t kMaxLevelOfTree = 16;

constexpr uint16_t kMaxCoro = MAX_CORO_NUM;
constexpr uint64_t rdmaBufferSize    = 1;         // GB  [CONFIG] 4
constexpr int64_t kPerThreadRdmaBuf  = rdmaBufferSize * define::GB / MAX_APP_THREAD;
constexpr int64_t kPerCoroRdmaBuf = kPerThreadRdmaBuf / kMaxCoro;

constexpr uint8_t kMaxHandOverTime = 8;

constexpr int kIndexCacheSize = 6000;

// KV
constexpr uint32_t keyLen = 8;
constexpr uint32_t simulatedValLen = 8;
} // namespace define

static inline unsigned long long asm_rdtsc(void) {
  unsigned hi, lo;
  __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
  return ((unsigned long long)lo) | (((unsigned long long)hi) << 32);
}

// For Tree
using Key = std::array<uint8_t, define::keyLen>;
using Value = uint64_t;
constexpr uint64_t kKeyMin = 1;
#ifdef KEY_SPACE_LIMIT
constexpr uint64_t kKeyMax = 60000000;  // only for int workloads
#endif
constexpr Value kValueNull = 0;
constexpr Value kValueMin = 1;
constexpr Value kValueMax = std::numeric_limits<Value>::max();
// fixed
constexpr int leafSpanSize = 128;
constexpr int internalSpanSize = 32;


// calculate kInternalPageSize and kLeafPageSize
constexpr int find_len_idx(uint32_t len) {
  return len == 8 ? 0 : (
          len == 16 ? 1 : (
            len == 32 ? 2 : (
              len == 64 ? 3 : (
                len == 128 ? 4 : (
                  len == 256 ? 5 : (
                    len == 512 ? 6 : (
                      len == 1024 ? 7 : -1
                    )
                  )
                )
              )
            )
          )
        );
}
constexpr int idx_1 = find_len_idx(define::keyLen);
constexpr int idx_2 = find_len_idx(define::simulatedValLen);
static_assert(idx_2 >= 0);

constexpr uint32_t headerSizes[8]        = {35, 51, 83, 147, 275, 531, 1043, 2067}; // keyLen: 8~1024
constexpr uint32_t internalEntrySizes[8] = {16, 24, 40, 72 , 136, 264, 520, 1032};  // keyLen: 8~1024
constexpr uint32_t leafEntrySizes[8][8]  = {{18, 26, 42, 74, 138, 266, 522, 1034}, {26}, {42, 50, 66, 98, 162, 290, 546, 1058}, {74}, {138}, {266}, {522}, {1034}}; // keyLen: 8~1024 valLen=8~1024

#ifdef TEST_FINE_GRAINED_LOCK
constexpr uint32_t kInternalPageSize = internalSpanSize * (internalEntrySizes[idx_1] + 8)    + headerSizes[idx_1] + 14;
constexpr uint32_t kLeafPageSize     = leafSpanSize * (leafEntrySizes[idx_1][idx_2] + 8) + headerSizes[idx_1] + 12;
#else
constexpr uint32_t kInternalPageSize = internalSpanSize * internalEntrySizes[idx_1]    + headerSizes[idx_1] + 14;
constexpr uint32_t kLeafPageSize     = leafSpanSize * leafEntrySizes[idx_1][idx_2] + headerSizes[idx_1] + 12;
#endif

__inline__ unsigned long long rdtsc(void) {
  unsigned hi, lo;
  __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
  return ((unsigned long long)lo) | (((unsigned long long)hi) << 32);
}

inline void mfence() { asm volatile("mfence" ::: "memory"); }

inline void compiler_barrier() { asm volatile("" ::: "memory"); }

#endif /* __COMMON_H__ */
