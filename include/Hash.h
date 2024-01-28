#if !defined(_HASH_H_)
#define _HASH_H_

#include "Common.h"
#include "Key.h"
#include "GlobalAddress.h"
#include "city.h"


inline uint64_t get_hashed_local_lock_index(const Key& k) {
  // return CityHash64((char *)&k, sizeof(k)) % define::kLocalLockNum;
  uint64_t res = 0, cnt = 0;
  for (auto a : k) if (cnt ++ < 8) res = (res << 8) + a;
  return res % define::kLocalLockNum;
}


inline uint64_t get_hashed_local_lock_index(const GlobalAddress& addr) {
  // return CityHash64((char *)&addr, sizeof(addr)) % define::kLocalLockNum;
  return addr.to_uint64() % define::kLocalLockNum;
}

#endif // _HASH_H_