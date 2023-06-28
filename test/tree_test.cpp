#include "DSM.h"
#include "Tree.h"

int main() {

  DSMConfig config;
  config.machineNR = 2;
  DSM *dsm = DSM::getInstance(config);
 
  dsm->registerThread();

  auto tree = new Tree(dsm);

  Value v;

  if (dsm->getMyNodeID() != 0) {
    while(true);
  }


  for (uint64_t i = 1; i < 10240; ++i) {
    tree->insert(int2key(i), i * 2);
  }
  printf("insert passed.\n");

  for (uint64_t i = 10240 - 1; i >= 1; --i) {
    tree->insert(int2key(i), i * 3);
  }

  printf("update passed.\n");

  for (uint64_t i = 1; i < 10240; ++i) {
    auto res = tree->search(int2key(i), v);
    assert(res && v == i * 3);
  }

  printf("search passed.\n");

  std::map<Key, Value> ret;
  tree->range_query(int2key(1), int2key(800), ret);
  for (uint64_t j = 1; j < 800; ++ j) assert(ret[int2key(j)] == j * 3);

  printf("range query passed.\n");
  printf("Hello\n");

  while (true)
    ;
}