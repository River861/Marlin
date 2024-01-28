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
#include <queue>

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

// DEBUG-TREE
// #define TREE_ENABLE_READ_DELEGATION
// #define TREE_ENABLE_WRITE_COMBINING

#define LATENCY_WINDOWS 100000
#define ALLOC_ALLIGN_BIT 8

#define STRUCT_OFFSET(type, field)                                             \
  (char *)&((type *)(0))->field - (char *)((type *)(0))

#define MAX_MACHINE 20
#define MEMORY_NODE_NUM 1
#define CPU_PHYSICAL_CORE_NUM 72  // [CONFIG] 72
#define MAX_KEY_SPACE_SIZE 60000000
// #define KEY_SPACE_LIMIT

#define ADD_ROUND(x, n) ((x) = ((x) + 1) % (n))

#define ROUND_UP(x, n) (((x) + (1<<(n)) - 1) & ~((1<<(n)) - 1))

#define MESSAGE_SIZE 96 // byte

#define POST_RECV_PER_RC_QP 4096

#define RAW_RECV_CQ_COUNT 4096

// #define STATIC_ID_FROM_IP

// { app thread
#define MAX_APP_THREAD 65    // one additional thread for data statistics(main thread)  [CONFIG] 65

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

using CoroQueue = std::queue<uint16_t>;

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
constexpr uint64_t dsmSize    = 64;        // GB  [CONFIG] 64
constexpr uint64_t kChunkSize = 16 * MB;

// for store root pointer
constexpr uint64_t kRootPointerStoreOffest = kChunkSize / 2;
static_assert(kRootPointerStoreOffest % sizeof(uint64_t) == 0, "XX");

// lock on-chip memory
constexpr uint64_t kLockStartAddr = 0;
constexpr uint64_t kLockChipMemSize = ON_CHIP_SIZE * 1024;
constexpr uint64_t kLocalLockNum    = 4 * MB;  // tune to an appropriate value (as small as possible without affect the performance)

// number of locks
// we do not use 16-bit locks, since 64-bit locks can provide enough concurrency.
// if you wan to use 16-bit locks, call *cas_dm_mask*
constexpr uint64_t kNumOfLock = kLockChipMemSize / sizeof(uint64_t);

// level of tree
constexpr uint64_t kMaxLevelOfTree = 16;

constexpr uint16_t kMaxCoro = MAX_CORO_NUM;
constexpr uint64_t rdmaBufferSize    = 4;         // GB  [CONFIG] 4
constexpr int64_t kPerThreadRdmaBuf  = rdmaBufferSize * define::GB / MAX_APP_THREAD;
constexpr int64_t kPerCoroRdmaBuf = kPerThreadRdmaBuf / kMaxCoro;

constexpr uint8_t kMaxHandOverTime = 8;

constexpr int kIndexCacheSize = 600;

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
constexpr int spanSize = 32;


// calculate kInternalPageSize and kLeafPageSize
constexpr uint32_t headerSize        = define::keyLen * 2 + 19;
constexpr uint32_t internalEntrySize = define::keyLen + 8;

constexpr uint32_t kInternalPageSize = spanSize * internalEntrySize + headerSize + 14;
constexpr uint32_t kLeafPageSize     = spanSize * (define::keyLen + define::simulatedValLen + 2) + headerSize + 12;

__inline__ unsigned long long rdtsc(void) {
  unsigned hi, lo;
  __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
  return ((unsigned long long)lo) | (((unsigned long long)hi) << 32);
}

inline void mfence() { asm volatile("mfence" ::: "memory"); }

inline void compiler_barrier() { asm volatile("" ::: "memory"); }

#endif /* __COMMON_H__ */
