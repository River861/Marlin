cmake_minimum_required(VERSION 3.10.2 FATAL_ERROR)
project(Sherman)

#Compiler options
# set(CMAKE_C_FLAGS "-Wall -Wno-deprecated-declarations -Wsign-compare -g")  # -DNDEBUG
set(CMAKE_C_FLAGS "-Wall -Wno-deprecated-declarations -Wno-unused-variable -Wno-unused-but-set-variable -Wsign-compare -O3 -g")
set(CMAKE_CXX_FLAGS "${CMAKE_C_FLAGS} -std=c++17")

# Link Options
set(LINKS_FLAGS "-lnuma -lcityhash -lboost_system -lboost_coroutine -lpthread -libverbs -lmemcached -ltbb")

#Env Options
option (STATIC_MN_IP "Use static MNs according the IPs of the nodes" OFF)
option (ENABLE_CORO "Turn on the coroutine" ON)
option (ENABLE_CACHE "Turn on the computing-side cache" ON)
option (LONG_TEST_EPOCH "Use big epoch num and long epoch duration" OFF)
option (SHORT_TEST_EPOCH "Use small epoch num and short epoch duration" OFF)
option (MIDDLE_TEST_EPOCH "Use middle epoch num and short epoch duration" OFF)
option (ENABLE_CACHE_EVICTION "Turn on cache-eviction" ON)
option (ON_CHIP "Enable on-chip locks" ON)
option (READ_DELEGATION "Turn on read delegation technique" OFF)
option (WRITE_COMBINING "Turn on write combining technique" OFF)

if(STATIC_MN_IP)
    add_definitions(-DSTATIC_ID_FROM_IP)
else()
    remove_definitions(-DSTATIC_ID_FROM_IP)
endif()

if(ENABLE_CORO)
    add_definitions(-DUSE_CORO)
else()
    remove_definitions(-DUSE_CORO)
endif()

if(ENABLE_CACHE)
    add_definitions(-DTREE_ENABLE_CACHE)
else()
    remove_definitions(-DTREE_ENABLE_CACHE)
endif()

if(LONG_TEST_EPOCH)
    add_definitions(-DLONG_TEST_EPOCH)
else()
    remove_definitions(-DLONG_TEST_EPOCH)
endif()

if(SHORT_TEST_EPOCH)
    add_definitions(-DSHORT_TEST_EPOCH)
else()
    remove_definitions(-DSHORT_TEST_EPOCH)
endif()

if(MIDDLE_TEST_EPOCH)
    add_definitions(-DMIDDLE_TEST_EPOCH)
else()
    remove_definitions(-DMIDDLE_TEST_EPOCH)
endif()

if(ENABLE_CACHE_EVICTION)
    add_definitions(-DNEED_CACHE_EVICTION)
else()
    remove_definitions(-DNEED_CACHE_EVICTION)
endif()

if(ON_CHIP)
    remove_definitions(-DCONFIG_ENABLE_EMBEDDING_LOCK)
else()
    add_definitions(-DCONFIG_ENABLE_EMBEDDING_LOCK)
endif()

if(READ_DELEGATION)
    add_definitions(-DTREE_ENABLE_READ_DELEGATION)
else()
    remove_definitions(-DTREE_ENABLE_READ_DELEGATION)
endif()

if(WRITE_COMBINING)
    remove_definitions(-DCONFIG_ENABLE_LOCK_HANDOVER)
    add_definitions(-DTREE_ENABLE_WRITE_COMBINING)
else()
    add_definitions(-DCONFIG_ENABLE_LOCK_HANDOVER)
    remove_definitions(-DTREE_ENABLE_WRITE_COMBINING)
endif()

#Tree Options
# Variable-length KV
option (ENABLE_VAR_LEN_KV "Turn on the support for variable-length KVs" OFF)
option (TREE_ENABLE_MARLIN "Turn on the designs of Marlin (ICPP'23)" OFF)

if(ENABLE_VAR_LEN_KV)
    add_definitions(-DENABLE_VAR_LEN_KV)
else()
    remove_definitions(-DENABLE_VAR_LEN_KV)
endif()

if(TREE_ENABLE_MARLIN)
    add_definitions(-DTREE_ENABLE_MARLIN)
else()
    remove_definitions(-DTREE_ENABLE_MARLIN)
endif()

set(INCLUDE_BASE ${PROJECT_SOURCE_DIR}/include)
include_directories(${INCLUDE_BASE})

#Source file define
set(COMMON_SRC ${PROJECT_SOURCE_DIR}/src)

#Used by both server and clients
file(GLOB_RECURSE COMMON_FILE ${COMMON_SRC}/*.cpp)
add_library(sherman STATIC ${COMMON_FILE})
link_libraries(sherman)

# test

file(GLOB TEST_SRC ${PROJECT_SOURCE_DIR}/test/*.cpp)
foreach (TEST ${TEST_SRC})
    get_filename_component(TEST_NAME ${TEST} NAME_WE)
    add_executable(${TEST_NAME} ${TEST})
    target_link_libraries(${TEST_NAME} ${LINKS_FLAGS})
endforeach()

