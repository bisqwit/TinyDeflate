# TinyDeflate

A deflate/gzip decompressor, as a C++11 template function,
that requires minimal amount of memory to work.

## Memory usage

* 160 bytes of automatic storage for length tables (320 elements, 4 bits each)
* 2160 bytes of automatic storage for huffman tree (638 elements, 27 bits each)
* 51 bytes of temporary automatic storage while a huffman tree is being generated (17 elements, 24 bits each)
* An assortment of automatic variables for various purposes (may be register variables, depending on the architecture and of the compiler wits)
* ABI mandated alignment losses

Total: 2320 bytes minimum, 2371+N bytes maximum

In addition, if you neither decompress into a raw memory area nor supply your own window function,
32768 bytes of automatic storage is allocated for the look-behind window.

## Unrequirements

* No dynamic memory is allocated under any circumstances, unless your user-supplied functors do it.
* The only #include is assert.h, for assert(). No other standard library function, template, or typedef is used.
* There are no constant arrays or global variables.

## Rationale

* Embedded platforms (Arduino, STM32 etc).
* ROM hacking

## Caveats

* Decompressor only. Deflate and GZIP streams are supported.
* Data is assumed to be valid. In case of invalid data, either an assert() will fail, or the program will write out of memory bounds.
* There is no way to prematurely abort decompression, other than by terminating the program (such as with a failing assertion).
* Slower than your average inflate function. The template uses densely bitpacked arrays, which require plenty of bit-shifting operations for every access.
* The code obviously performs best on 32-bit or 64-bit platforms. Platforms where 32-bit entities must be synthesized from a number of 8-bit entities are at a disadvantage.
