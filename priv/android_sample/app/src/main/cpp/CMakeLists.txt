cmake_minimum_required(VERSION 3.22.1)
project(bookstore_native LANGUAGES C CXX)


set(CMAKE_ANDROID_STL_TYPE c++_shared)


add_library(native-lib SHARED native-lib.cpp)


set_target_properties(native-lib PROPERTIES OUTPUT_NAME native-lib)


find_library(log-lib log)
find_library(dl-lib dl)


target_link_libraries(
        native-lib
        c++_shared
        ${log-lib}
        ${dl-lib}
)
