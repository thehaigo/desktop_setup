cmake_minimum_required(VERSION 3.22.1)
project(template_app_native LANGUAGES C CXX)


set(CMAKE_ANDROID_STL_TYPE c++_shared)


add_library(app SHARED native-lib.cpp)

set(ANDROID_RUNTIME_DIR "${CMAKE_CURRENT_LIST_DIR}/../../../../erlang-libs")
set(LIBERLANG_A "${ANDROID_RUNTIME_DIR}/${ANDROID_ABI}/liberlang.a")

if (NOT EXISTS "${LIBERLANG_A}")
    message(FATAL_ERROR "Missing ${LIBERLANG_A}. Ensure android-runtime libs are present.")
endif()

add_library(liberlang_static STATIC IMPORTED)
set_target_properties(liberlang_static PROPERTIES IMPORTED_LOCATION "${LIBERLANG_A}")

add_library(liberlang_shared SHARED empty.c ei_md5.c)
set_target_properties(liberlang_shared PROPERTIES OUTPUT_NAME "erlang")


set_target_properties(app PROPERTIES OUTPUT_NAME app)


find_library(log-lib log)
find_library(dl-lib dl)


target_link_libraries(
        app
        c++_shared
        ${log-lib}
        ${dl-lib}
        android
)

target_link_libraries(
        liberlang_shared
        -Wl,--whole-archive
        liberlang_static
        -Wl,--no-whole-archive
        c++_shared
        ${log-lib}
        ${dl-lib}
        android
)

add_dependencies(app liberlang_shared)
