#include "test.h"

typedef struct shape {
  int n;
  int c;
  int h;
  int w;
} shape_t;

typedef struct stride {
  int c;
  int h;
  int w;
} stride_t;

typedef struct buffer {
  shape_t shape;
  int addr;
} buffer_t;

shape_t pack_shape(int n, int c, int h, int w) {
  shape_t s = {n, c, h, w};
  return s;
}

stride_t pack_stride(int c, int h, int w) {
  stride_t s = {c, h, w};
  return s;
}

// I.L2_STORE_CONF(stride_t.ss1, stride_t.ss1, L2_DATATYPE.i16,
// DDR_DATATYPE.i16);

void l2_store_conf(stride_t rstride_d, stride_t rstride_s, int l2_datatype,
                   int ddr_datatype) {
}

void main(buffer_t input, buffer_t output) {
  stride_t i_s = pack_stride(2, 2, 2);

  I.L2_STORE_CONF(stride_t.ss1, stride_t.ss1, L2_DATATYPE.i16,
                  DDR_DATATYPE.i16),
}