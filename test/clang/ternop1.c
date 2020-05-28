typedef signed int __int32_t;

extern const __int32_t **__ctype_tolower_loc(void)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__const__));

extern __inline __attribute__((__gnu_inline__)) int
    __attribute__((__nothrow__, __leaf__)) tolower(int __c) {
  return __c >= -128 && __c < 256 ? (*__ctype_tolower_loc())[__c] : __c;
}
