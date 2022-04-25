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
)

add_compile_options(-std=c11 -fno-common -Wall -Wno-switch)

add_executable(chibicc ${SRC})