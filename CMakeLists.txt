cmake_minimum_required(VERSION 3.10.2 FATAL_ERROR)
project(Sherman)

# set (CMAKE_C_COMPILER "/usr/local/openmpi/bin/mpicxx")
# set (CMAKE_CXX_COMPILER ${CMAKE_C_COMPILER})

#Compiler options
set(CMAKE_C_FLAGS "-Wall -Wno-deprecated-declarations -Wsign-compare -g")  # -DNDEBUG
# set(CMAKE_C_FLAGS "-Wall -Wno-deprecated-declarations -Wno-unused-variable -Wno-unused-but-set-variable -Wsign-compare -O3 -g")
set(CMAKE_CXX_FLAGS "${CMAKE_C_FLAGS} -std=c++11 ")

# Link Options
set(LINKS_FLAGS "-lcityhash -lboost_system -lboost_coroutine -lpthread -libverbs -lmemcached -ltbb")

# option (SANITIZE "Turn on sanitization" ON)
# if (SANITIZE)
    # set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address")
# endif()

#Env Options
option (STATIC_MN_IP "Use static MNs according the IPs of the nodes" OFF)
option (ENABLE_CACHE "Turn on the computing-side cache" ON)
option (LONG_TEST_EPOCH "Use big epoch num and long epoch duration" OFF)
option (SHORT_TEST_EPOCH "Use small epoch num and short epoch duration" OFF)
option (MIDDLE_TEST_EPOCH "Use middle epoch num and short epoch duration" OFF)
option (ENABLE_CACHE_EVICTION "Turn on cache-eviction" ON)

if(STATIC_MN_IP)
    add_definitions(-DSTATIC_ID_FROM_IP)
else()
    remove_definitions(-DSTATIC_ID_FROM_IP)
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

#On-chip Options
option (ON_CHIP "Enable on-chip locks" ON)
if(ON_CHIP)
    add_definitions(-DCONFIG_ENABLE_LOCK_HANDOVER)
    remove_definitions(-DCONFIG_ENABLE_EMBEDDING_LOCK)
else()
    remove_definitions(-DCONFIG_ENABLE_LOCK_HANDOVER)
    add_definitions(-DCONFIG_ENABLE_EMBEDDING_LOCK)
endif()

#Simulation Options
option (RM_LEAF_AMPLIFICATION "Simulate a B+ tree w/o read amplification in leaf nodes" OFF)
option (RM_INTERNAL_AMPLIFICATION "Simulate a B+ tree w/o read amplification in internal nodes" OFF)
option (TEST_FINE_GRAINED_LOCK "Simulate a B+ tree with fine-grained locks" OFF)
if(RM_LEAF_AMPLIFICATION)
    add_definitions(-DRM_LEAF_AMPLIFICATION)
else()
    remove_definitions(-DRM_LEAF_AMPLIFICATION)
endif()

if(RM_INTERNAL_AMPLIFICATION)
    add_definitions(-DRM_INTERNAL_AMPLIFICATION)
else()
    remove_definitions(-DRM_INTERNAL_AMPLIFICATION)
endif()

if(TEST_FINE_GRAINED_LOCK)
    add_definitions(-DTEST_FINE_GRAINED_LOCK)
else()
    remove_definitions(-DTEST_FINE_GRAINED_LOCK)
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

