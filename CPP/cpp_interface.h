#ifndef CPP_INTERFACE
#define CPP_INTERFACE
#ifdef __cplusplus
void cpp_smoketest();
extern "C" void c_smoketest();
void c_smoketest()
{
  cpp_smoketest();
}
#endif
#endif
