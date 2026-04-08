cmake_minimum_required(VERSION 3.10)
project(malloclab C)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -O2 -Wall -g -DDRIVER")

file(GLOB SOURCES "*.c")
add_executable(code ${SOURCES})
