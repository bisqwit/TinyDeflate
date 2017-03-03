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

## Tuning

If you can afford more RAM, there are three options in gunzip.hh that you can change:

* USE_BITARRAY_TEMPORARY_IN_HUFFMAN_CREATION : Change this to false to use additional 12 bytes of memory for a tiny boost in performance.
* USE_BITARRAY_FOR_LENGTHS : Change this to false to use additional 160 bytes of memory for a noticeable boost in performance.
* USE_BITARRAY_FOR_HUFFNODES : Change this to false to use additional 392 bytes of memory for a significant boost in performance.

All three settings at 'false' will consume 2940 bytes of automatic memory + alignment losses + callframes + spills.

## Example use:

Decompress the standard input into the standard output (uses 32 kB automatically allocated window):

    Deflate([]()                   { return std::getchar(); },
            [](unsigned char byte) { std::putchar(byte); });
    
    // Or more simply:
    
    Deflate(std::getchar, std::putchar);

Decompress an array containing gzipped data into another array that must be large enough to hold the result. A window buffer will not be allocated.

    extern const char compressed_data[];
    extern unsigned char outbuffer[131072];

    unsigned inpos = 0;
    Deflate([&]() { return compressed_data[inpos++]; },
            outbuffer);

Decompress using a custom window function (the separate 32 kB window buffer will not be allocated):

    std::vector<unsigned char> result;

    Deflate(std::getchar,
            [&](unsigned byte)
            {
                result.push_back(byte);
            },
            [&](unsigned length, unsigned offset)
            {
                 if(!length)
                 {
                     // offset contains the maximum look-behind distance.
                     // You could use this information to allocate a buffer of a particular size.
                     // length=0 case is invoked exactly once before any length!=0 cases are.
                 }
                 while(length-- > 0)
                 {
                     result.push_back( result[result.size()-offset] );
                 }
            });
