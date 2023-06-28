#if !defined(_KEY_H_)
#define _KEY_H_

#include "Common.h"


// inline void add_one(Key& a) {
//   for (int i = 0; i < (int)define::keyLen; ++ i) {
//     auto& partial = a.at(define::keyLen - 1 - i);
//     if ((int)partial + 1 < (1 << 8)) {
//       partial ++;
//       return;
//     }
//     else {
//       partial = 0;
//     }
//   }
// }

inline Key operator+(const Key& a, uint8_t b) {
  Key res = a;
  for (int i = 0; i < (int)define::keyLen; ++ i) {
    auto& partial = res.at(define::keyLen - 1 - i);
    if ((int)partial + b < (1 << 8)) {
      partial += b;
      break;
    }
    else {
      auto tmp = ((int)partial + b);
      partial = tmp % (1 << 8);
      b = tmp / (1 << 8);
    }
  }
  return res;
}

inline Key operator-(const Key& a, uint8_t b) {
  Key res = a;
  for (int i = 0; i < (int)define::keyLen; ++ i) {
    auto& partial = res.at(define::keyLen - 1 - i);
    if (partial >= b) {
      partial -= b;
      break;
    }
    else {
      int carry = 0, tmp = partial;
      while(tmp < b) tmp += (1 << 8), carry ++;
      partial = ((int)partial + carry * (1 << 8)) - b;
      b = carry;
    }
  }
  return res;
}

inline Key int2key(uint64_t key) {
#ifdef KEY_SPACE_LIMIT
  key = key % (kKeyMax - kKeyMin) + kKeyMin;
#endif
  if (key == 0) key ++;  // key != 0
  Key res{};
  for (int i = 1; i <= (int)define::keyLen; ++ i) {
    auto shr = (define::keyLen - i) * 8;
    res.at(i - 1) = (shr >= 64u ? 0 : ((key >> shr) & ((1 << 8) - 1))); // Is equivalent to padding zero for short key
  }
  return res;
}

inline Key str2key(const std::string &key) {
  // assert(key.size() <= define::keyLen);
  Key res{};
  std::copy(key.begin(), key.size() <= define::keyLen ? key.end() : key.begin() + define::keyLen, res.begin());
  return res;
}

inline uint64_t key2int(const Key& key) {
  uint64_t res = 0;
  for (auto a : key) res = (res << 8) + a;
  return res;
}

inline std::ostream &operator<<(std::ostream &os, const Key &k) {
  for (auto i : k) os << i << "-";
  return os;
}

#endif // _KEY_H_
