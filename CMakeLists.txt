cmake_minimum_required(VERSION 3.11)
project(chibicc)
enable_language(C)

set(SRC
  hashmap.c
  main.c
  parse.c
  preprocess.c
  strings.c
  tokenize.c
  type.c
  unicode.c
  codegen.c
)

add_compile_options(-std=c11 -g -fno-common -Wall -Wno-switch)

add_definitions(-DSTACK_SIZE=262144)
add_definitions(-DSOURCE_PATH=\"${CMAKE_CURRENT_SOURCE_DIR}\")

add_executable(chibicc ${SRC})