# TinyDeflate

A deflate/gzip decompressor, as a C++14 template function,
that requires minimal amount of memory to work.

    Terms of use: Zlib    
    Copyright © 2017 Joel Yliluoma

## Memory usage at aggressive settings

* 160 bytes of automatic storage for length tables (320 elements)
* 384 bytes of automatic storage for huffman tree (352 elements)
* 24 bytes of temporary automatic storage while a huffman tree is being generated (16 elements)
* An assortment of automatic variables for various purposes (may be register variables, depending on the architecture and of the compiler wits)
* ABI mandated alignment losses

Total: 544 bytes minimum, 568+N bytes maximum

In addition, if you neither decompress into a raw memory area nor supply your own window function,
32768 bytes of automatic storage is allocated for the look-behind window.

## Memory usage at default settings

* 320 bytes of automatic storage for length tables (320 elements)
* 640 bytes of automatic storage for huffman tree (352 elements)
* 32 bytes of temporary automatic storage while a huffman tree is being generated (16 elements)
* An assortment of automatic variables for various purposes (may be register variables, depending on the architecture and of the compiler wits)
* ABI mandated alignment losses

Total: 960 bytes minimum, 992+N bytes maximum

In addition, if you neither decompress into a raw memory area nor supply your own window function,
32768 bytes of automatic storage is allocated for the look-behind window.

## Tuning

To adjust the memory usage, there are three settings in gunzip.hh you can change:

| Setting name | 'false' memory use bytes | 'true' memory use bytes | 'true' performance impact
| ------------------------------------------- | ---:| ----:|--------------
| **USE_BITARRAY_TEMPORARY_IN_HUFFMAN_CREATION** |  32 | 24  | Negligible
| **USE_BITARRAY_FOR_LENGTHS**                   | 320 | 160 | Noticeable
| **USE_BITARRAY_FOR_HUFFNODES**                 | 640 | 384 | Significant
| **Total**                                      | 992 | 568 | _Plus alignment losses, callframes and spills_

## Unrequirements

* No dynamic memory is allocated under any circumstances, unless your user-supplied functors do it.
* Aside from assert() in assert.h and some template metaprogramming tools in type_traits, no standard library functions are used.
* No global variables.
* Compatible with -fno-exceptions -fno-rtti compilation.
* Option to compile without constant arrays.

## Rationale

* Embedded platforms (Arduino, STM32 etc).
* ROM hacking

## Caveats

* Decompressor only. Deflate and GZIP streams are supported.
* Slower than your average inflate function. The template uses densely bitpacked arrays, which require plenty of bit-shifting operations for every access.
* The code obviously performs best on 32-bit or 64-bit platforms. Platforms where 32-bit entities must be synthesized from a number of 8-bit entities are at a disadvantage.

## Definitions

```C++
// Most generic: Input and output functors
template<typename InputFunctor, typename OutputFunctor>
int Deflate(InputFunctor&& input, OutputFunctor&& output); // (1) (5) (9)

// An optional window functor can be supplied, so the lib will not allocate 32768-byte look-behind buffer
template<typename InputFunctor, typename OutputFunctor, typename WindowFunctor>
int Deflate(InputFunctor&& input, OutputFunctor&& output, WindowFunctor&& outputcopy); // (2) (5)

// Output iterator (write only)
template<typename InputFunctor, typename OutputIterator>
int Deflate(InputFunctor&& input, OutputIterator&& target); // (5) (9)

// Random-access iterator. It is also used for reading (look-behinds).
template<typename InputFunctor, typename RandomAccessIterator>
int Deflate(InputFunctor&& input, RandomAccessIterator&& target); // (5) (10)

template<typename InputFunctor, typename RandomAccessIterator>
int Deflate(InputFunctor&& input, RandomAccessIterator&& target, std::size_t target_limit); // (3) (5) (10)

template<typename InputFunctor, typename RandomAccessIterator>
int Deflate(InputFunctor&& input, RandomAccessIterator&& target_begin, RandomAccessIterator&& target_end); // (4) (5) (10)


// These are the same as the first six,
// but instead of an input functor, they use an input iterator.
// An input iterator is dereferenced and read at most once (per byte), and then incremented.

template<typename InputIterator, typename OutputFunctor>
int Deflate(InputIterator&& input, OutputFunctor&& output); // (1) (7) (9)

template<typename InputIterator, typename OutputFunctor, typename WindowFunctor>
int Deflate(InputIterator&& input, OutputFunctor&& output, WindowFunctor&& outputcopy); // (2) (7)

template<typename InputIterator, typename OutputIterator>
int Deflate(InputIterator&& input, OutputIterator&& target); // (7) (9)

template<typename InputIterator, typename RandomAccessIterator>
int Deflate(InputIterator&& input, RandomAccessIterator&& target); // (7) (10)

template<typename InputIterator, typename RandomAccessIterator>
int Deflate(InputIterator&& input, RandomAccessIterator&& target, std::size_t target_limit); // (3) (7) (10)

template<typename InputIterator, typename RandomAccessIterator>
int Deflate(InputIterator&& input, RandomAccessIterator&& target_begin, RandomAccessIterator&& target_end); // (4) (7) (10)


// These are the same as the first six, but instead of an input functor,
// they use a pair of forward iterators to indicate the range of input data.
// Forward iterators are used like input iterators, but two iterators can be compared for equality.

template<typename ForwardIterator, typename OutputFunctor>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputFunctor&& output); // (1) (6) (9)

template<typename ForwardIterator, typename OutputFunctor, typename WindowFunctor>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputFunctor&& output, WindowFunctor&& outputcopy); // (2) (6)

template<typename ForwardIterator, typename OutputIterator>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputIterator&& target); // (6) (9)

template<typename ForwardIterator, typename RandomAccessIterator>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, RandomAccessIterator&& target); // (6) (10)

template<typename ForwardIterator, typename RandomAccessIterator>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, RandomAccessIterator&& target, std::size_t target_limit); // (3) (6) (10)

template<typename ForwardIterator, typename RandomAccessIterator>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, RandomAccessIterator&& target_begin, RandomAccessIterator&& target_end); // (4) (6) (10)


// These are the same as the first six, but instead of an input functor,
// they use an input iterator and a length.

template<typename InputIterator, typename OutputFunctor>
int Deflate(InputIterator&& begin, std::size_t length, OutputFunctor&& output); // (1) (7) (8) (9)

template<typename InputIterator, typename OutputFunctor, typename WindowFunctor>
int Deflate(InputIterator&& begin, std::size_t length, OutputFunctor&& output, WindowFunctor&& outputcopy); // (2) (7) (8)

template<typename InputIterator, typename OutputIterator>
int Deflate(InputIterator&& begin, std::size_t length, OutputIterator&& target); // (7) (8) (9)

template<typename InputIterator, typename RandomAccessIterator>
int Deflate(InputIterator&& begin, std::size_t length, RandomAccessIterator&& target); // (7) (8) (10)

template<typename InputIterator, typename RandomAccessIterator>
int Deflate(InputIterator&& begin, std::size_t length, RandomAccessIterator&& target, std::size_t target_limit); // (3) (7) (8) (10)

template<typename InputIterator, typename RandomAccessIterator>
int Deflate(InputIterator&& begin, std::size_t length, RandomAccessIterator&& target_begin, RandomAccessIterator&& target_end); // (4) (7) (8) (10)


// Finally, the following three patterns are available, if you need to know
// after decompression how many bytes were read and/or written:

struct DeflateTrackNoSize{};
struct DeflateTrackInSize{};
struct DeflateTrackOutSize{};
struct DeflateTrackBothSize{};

template<typename... Args>
int Deflate(Args&&... args, DeflateTrackNoSize); // (Same as no tag)

template<typename... Args>
std::pair<int, std::uint_fast64_t> Deflate(Args&&... args, DeflateTrackInSize); // (11)

template<typename... Args>
std::pair<int, std::uint_fast64_t> Deflate(Args&&... args, DeflateTrackOutSize); // (12)

template<typename... Args>
std::pair<int, std::pair<std::uint_fast64_t,std::uint_fast64_t>> Deflate(Args&&... args, DeflateTrackBothSize); // (13)

// A counter for sizes is only allocated if explicitly requested by using one of these three overloads.
```

1) If the output functor (`output`) returns a `bool`, and the returned value is `true`, the decompression aborts with return value -3
without writing any more data.

2) If the output functor (`output`) returns a `bool`, and the returned value is `true`, the decompression aborts with return value -3
without writing any more data.
If the window function returns an integer type, and the returned value is other than 0, the decompression aborts with return value -4
without writing any more data.
If either the window function returns `void`, or the output functor does not return a `bool`, aborting on output-full will not be compiled.

3) If `target_limit` bytes have been written into `target` and the decompression is not yet complete, the decompression aborts with return value -3
without writing any more data.

4) If `target_begin == target_end`, the decompression aborts with return value -3
without writing any more data.

5) If the input functor (`input`) returns an integer type other than a `char`, `signed char`, or `unsigned char`,
and the returned value is smaller than 0 or larger than 255, the decompression aborts with return value -2
without reading any more data.

6) If `begin == end`, the decompression aborts with return value -2.

7) If the input iterator deferences into a value outside the 0 — 255 range, the decompression aborts with return value -2
without reading any more data.

8) If `length` bytes have been read from `begin` and the decompression is not yet complete, the decompression aborts with return value -2
without reading any more data.

9) A separate 32768-byte sliding window will be automatically and separately allocated for the decompression.

10) The output data buffer is assumed to persist during the call and doubles as the sliding window for the decompression.

11) The `first` field in the return value has the same meaning as the `int` type return value described earlier.    
The `second` field in the return value contains the number of bytes that were consumed from the input.

12) The `first` field in the return value has the same meaning as the `int` type return value described earlier.    
The `second` field in the return value contains the number of bytes that were written to the output.

13) The `first` field in the return value has the same meaning as the `int` type return value described earlier.    
The `second.first` field in the return value contains the number of bytes that were consumed from the input.    
The `second.second` field in the return value contains the number of bytes that were written to the output.

### Tips

Some of these definitions may be ambiguous.
If you hit a compiler error, choose a different call method.
To help distinguish between (`InputIterator`,`RandomAccessIterator`,`RandomAccessIterator`)
and (`ForwardIterator`,`ForwardIterator`,`OutputIterator`), make sure the input iterators
are _const_.

If you do multiple decompression calls in your program in different spots,
it may be wise to make sure they all use the same type of parameters,
to avoid having to instantiate multiple copies of `Deflate()`.
Lambda functors are an offender in this respect, because each lambda has a
unique type even if their contents and calling conventions are identical.
In the worst case, you can use `std::function` to wrap your calls
into a common interface. Check out this video for more about this topic: https://www.youtube.com/watch?v=rUB5Hlm9AaQ

## Requirements

```C++
// An InputFunctor has the following prototype,
// wherein type1 is convertible into unsigned char:
type1 input()

// An OutputFunctor has one of the following two prototypes,
// wherein type1 can accept unsigned int parameters in range 0-255:
void output(type1 byte_to_output)
bool output(type1 byte_to_output)

// A WindowFunctor has one of the following two prototypes,
// wherein type1 can accept unsigned int parameters in range 0-258,
// and     type2 can accept unsigned int parameters:
void  outputcopy(type1 length, type2 offs)
type2 outputcopy(type1 length, type2 offs)

// An InputIterator must have at least the following operations defined,
// where type1 is convertible into unsigned char:
const type1& operator*() const
InputIterator& operator++()

// A OutputIterator must have at least the following operations defined,
// where type1 is convertible into unsigned char:
type1& operator*() const
OutputIterator& operator++()

// A ForwardIterator must have at least the following operations defined,
// where type1 is convertible into unsigned char:
const type1& operator*() const
ForwardIterator& operator++()
bool operator==(const ForwardIterator&) const

// A RandomAccessIterator must have at least the following operations defined,
// where type1 is convertible into unsigned char,
// and type2 is a signed integer type (may be negative):
type1& operator*()
type1& operator[] (type2)
RandomAccessIterator operator- (type2)
RandomAccessIterator& operator++()
bool operator==(const RandomAccessIterator&) const
```

## Example use:

Decompress the standard input into the standard output (uses 32 kB automatically allocated window):

```C++
    Deflate([]()                   { return std::getchar(); },
            [](unsigned char byte) { std::putchar(byte); });
    
    // Or more simply:
    
    Deflate(std::getchar, std::putchar);
```

Decompress an array containing gzipped data into another array that must be large enough to hold the result.
A window buffer will not be allocated.

```C++
    extern const char compressed_data[];
    extern unsigned char outbuffer[131072];
    
    Deflate(compressed_data+0, outbuffer+0);
```

Same as above, but with range checking for output, and reporting of written size:

```C++
    extern const char compressed_data[];
    extern unsigned char outbuffer[131072];
    
    auto result = Deflate(compressed_data+0, outbuffer+0, sizeof(outbuffer), DeflateTrackOutSize{});
    if(result.first != 0) std::fprintf(stderr, "Error %d\n", result.first);
    std::fprintf(stderr, "%u bytes written\n", unsigned(result.second));
```

Same as above, but with range checking for both input and output:

```C++
    extern const char compressed_data[];
    extern unsigned compressed_data_length;
    extern unsigned char outbuffer[131072];
    
    int result = Deflate(compressed_data+0, compressed_data_length, outbuffer, outbuffer + sizeof(outbuffer));
    if(result != 0) std::fprintf(stderr, "Error\n");
```

Decompress using a custom window function (the separate 32 kB window buffer will not be allocated):

```C++
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
```

Same as above, but stop decompressing once 4096 bytes have been written:

```C++
    std::vector<unsigned char> result;
    
    Deflate(std::getchar,
            [&](unsigned byte)
            {
                if(result.size() >= 4096) return true;
                result.push_back(byte);
                return false;
            },
            [&](unsigned length, unsigned offset)
            {
                 if(!length)
                 {
                     // offset contains the maximum look-behind distance.
                     // You could use this information to allocate a buffer of a particular size.
                     // length=0 case is invoked exactly once before any length!=0 cases are.
                 }
                 for(; result.size() < 4096 && length > 0; --length)
                 {
                     result.push_back( result[result.size()-offset] );
                 }
                 return length;
            });
```
