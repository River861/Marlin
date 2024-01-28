#ifndef __GLOBALADDRESS_H__
#define __GLOBALADDRESS_H__

#include "Common.h"


class GlobalAddress {
public:

union {
  struct {
  uint64_t nodeID: 16;
  uint64_t offset : 48;
  };
  uint64_t val;
};

  GlobalAddress() : val(0) {}
  GlobalAddress(uint64_t nodeID, uint64_t offset) : nodeID(nodeID), offset(offset) {}
  GlobalAddress(uint64_t val) : val(val) {}
  GlobalAddress(const GlobalAddress& gaddr) : val(gaddr.val) {}

  uint64_t to_uint64() const {return val; }

  static GlobalAddress Null() {
    static GlobalAddress zero{0, 0};
    return zero;
  };
} __attribute__((packed));

static_assert(sizeof(GlobalAddress) == sizeof(uint64_t), "XXX");

inline GlobalAddress GADD(const GlobalAddress &addr, int off) {
  auto ret = addr;
  ret.offset += off;
  return ret;
}

inline bool operator==(const GlobalAddress &lhs, const GlobalAddress &rhs) {
  return (lhs.nodeID == rhs.nodeID) && (lhs.offset == rhs.offset);
}

inline bool operator!=(const GlobalAddress &lhs, const GlobalAddress &rhs) {
  return !(lhs == rhs);
}

inline std::ostream &operator<<(std::ostream &os, const GlobalAddress &obj) {
  os << "[" << (int)obj.nodeID << ", 0x" << std::hex << obj.offset << std::dec << "]";
  return os;
}

#endif /* __GLOBALADDRESS_H__ */
