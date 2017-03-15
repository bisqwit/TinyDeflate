/* My tiny gzip decompressor without using zlib. - Joel Yliluoma
 * http://iki.fi/bisqwit/ , http://youtube.com/user/Bisqwit
 * Inspired and influenced by a 13th IOCCC winner program by Ron McFarland */
/* Further optimized based on ideas from tinf library by Joergen Ibsen */

/* Fun fact: Contains zero new/delete, and no STL data structures */
/* Distributed under the terms of the Zlib license:

  Copyright (C) 2017 Joel Yliluoma

  This software is provided 'as-is', without any express or implied
  warranty.  In no event will the authors be held liable for any damages
  arising from the use of this software.

  Permission is granted to anyone to use this software for any purpose,
  including commercial applications, and to alter it and redistribute it
  freely, subject to the following restrictions:

  1. The origin of this software must not be misrepresented; you must not
     claim that you wrote the original software. If you use this software
     in a product, an acknowledgment in the product documentation would be
     appreciated but is not required.
  2. Altered source versions must be plainly marked as such, and must not be
     misrepresented as being the original software.
  3. This notice may not be removed or altered from any source distribution.
*/
#include <assert.h>
#include <utility>     // std::forward
#include <cstdint>     // integer sizes
#include <type_traits>
#include <iterator>

#if !1 //Documentation purposes only; the actual prototypes are littered with std::enable_ifs.
// Deflate(): This is the public method declared (later) in this file.
// Decompresses (inflates) deflate-compressed data, with a gzip or deflate header.
// User-supplied functors:
//   input() returns the next byte from the (compressed) input.
//   output(byte) outputs one uncompressed byte.
//   outputcopy(length, offset) copies length uncompressed bytes from offset,
//       Offset is always >= 1.
//       offset 1 means previous byte,
//       offset 2 means previous before that and so on.
//       Note that (offset < length) is not an error and in fact happens frequently.
//       If length=0, offset indicates the largest look-behind window length that
//       you need to be prepared for. The length is a power-of-two in range 256..32768.
//
// If you want to implement range checking in input, return a negative value
// from input() when there is no more input.
//
// If you want to implement range checking in output, add a return value
// in output(): false=ok, true=abort; and a return value in outputcopy():
// 0=ok, nonzero=one or more bytes were not writable.
//
// Results:
//       0 = decompression complete
//      -1 = data error
//      -2 = input functor returned a value outside 0x00..0xFF range
//      -3 = output functor returned nonzero / bool true value
//      -4 = outputcopy functor returned nonzero remaining length value
//
template<typename InputFunctor, typename OutputFunctor, typename WindowFunctor>
int Deflate(InputFunctor&& input, OutputFunctor&& output, WindowFunctor&& outputcopy);

// Check README.md for the full list of versions of Deflate() available.

#endif

struct DeflateTrackTagBase{};
struct DeflateTrackNoSize: public DeflateTrackTagBase{};
struct DeflateTrackInSize: public DeflateTrackTagBase{};
struct DeflateTrackOutSize: public DeflateTrackTagBase{};
struct DeflateTrackBothSize: public DeflateTrackTagBase{};


// The rest of the file is just for the curious about implementation.
namespace gunzip_ns
{
    // If you want more performance at the expense of RAM use,
    // Turn one or more of these settings to false:
    static constexpr bool USE_BITARRAY_TEMPORARY_IN_HUFFMAN_CREATION = false; /* 8 bytes save */
    static constexpr bool USE_BITARRAY_FOR_LENGTHS = false;                   /* 160 bytes save */
    static constexpr bool USE_BITARRAY_FOR_HUFFNODES = false;                 /* 392 bytes save */

    static constexpr unsigned MAX_WINDOW_SIZE = 32768u;

    static_assert(MAX_WINDOW_SIZE >= 2,      "Max window size should be >= 2");
    static_assert(MAX_WINDOW_SIZE <= 32768u, "Window sizes larger than 32768 are not supported by deflate standard. Edit the source code to remove this assert if you need it.");

    // 
    #define DEFLATE_USE_DATA_TABLES

    #if !defined(DEFLATE_ALLOCATION_AUTOMATIC) && !defined(DEFLATE_ALLOCATION_STATIC) && !defined(DEFLATE_ALLOCATION_DYNAMIC)
    // Choose one:
    #define DEFLATE_ALLOCATION_AUTOMATIC
    //#define DEFLATE_ALLOCATION_STATIC
    //#define DEFLATE_ALLOCATION_DYNAMIC
    #endif
}

#define DeflIsInputFunctor  (std::is_convertible<std::result_of_t<std::decay_t<InputFunctor>()>,int>::value /*\
                             && !std::is_pointer<std::decay_t<InputFunctor>>::value*/)
#define DeflIsOutputFunctor        (std::is_same<std::result_of_t<std::decay_t<OutputFunctor>(int)>,void>::value \
                                 || std::is_convertible<std::result_of_t<std::decay_t<OutputFunctor>(int)>,bool>::value)
#define DeflIsWindowFunctor        (std::is_convertible<std::result_of_t<std::decay_t<WindowFunctor>(int,int)>,int>::value \
                                        || std::is_same<std::result_of_t<std::decay_t<WindowFunctor>(int,int)>,void>::value)

#define DeflIsForwardIterator   (std::is_convertible<typename std::iterator_traits<std::decay_t<ForwardIterator>>::value_type, unsigned char>::value \
                                    && (std::is_same<typename std::iterator_traits<std::decay_t<ForwardIterator>>::iterator_category, std::forward_iterator_tag>::value \
                                     || std::is_same<typename std::iterator_traits<std::decay_t<ForwardIterator>>::iterator_category, std::bidirectional_iterator_tag>::value \
                                     || std::is_same<typename std::iterator_traits<std::decay_t<ForwardIterator>>::iterator_category, std::random_access_iterator_tag>::value))

#define DeflIsInputIterator     (std::is_convertible<typename std::iterator_traits<std::decay_t<InputIterator>>::value_type, unsigned char>::value)

#define DeflIsRandomAccessIterator (std::is_convertible<typename std::iterator_traits<std::decay_t<RandomAccessIterator>>::value_type, unsigned char>::value \
                                  && !std::is_const<typename std::iterator_traits<std::decay_t<RandomAccessIterator>>::reference>::value \
                                    && std::is_same<typename std::iterator_traits<std::decay_t<RandomAccessIterator>>::iterator_category, std::random_access_iterator_tag>::value)

#define DeflIsOutputIterator    (std::is_convertible<typename std::iterator_traits<std::decay_t<OutputIterator>>::value_type, unsigned char>::value \
                                   && !std::is_const<typename std::iterator_traits<std::decay_t<OutputIterator>>::reference>::value \
                                   && !std::is_pointer<std::decay_t<OutputIterator>>::value \
                                    && (std::is_same<typename std::iterator_traits<std::decay_t<OutputIterator>>::iterator_category, std::output_iterator_tag>::value \
                                     || std::is_same<typename std::iterator_traits<std::decay_t<OutputIterator>>::iterator_category, std::forward_iterator_tag>::value \
                                     || std::is_same<typename std::iterator_traits<std::decay_t<OutputIterator>>::iterator_category, std::bidirectional_iterator_tag>::value))

#define DeflIsSizeType           (std::is_convertible<std::decay_t<SizeType>, std::size_t>::value \
                                  && !std::is_pointer<std::decay_t<SizeType>>::value)
#define DeflIsSizeType2          (std::is_convertible<std::decay_t<SizeType2>, std::size_t>::value \
                                  && !std::is_pointer<std::decay_t<SizeType2>>::value)
#define DeflIsTrackTag           (std::is_base_of<DeflateTrackTagBase, std::decay_t<SizeTrackTag>>::value)

#define DeflInputAbortable_InputFunctor \
                                 (1* !(std::is_same<std::decay_t<std::result_of_t<InputFunctor()>>, unsigned char>::value \
                                    || std::is_same<std::decay_t<std::result_of_t<InputFunctor()>>,   signed char>::value \
                                    || std::is_same<std::decay_t<std::result_of_t<InputFunctor()>>,          char>::value))
#define DeflOutputAbortable_OutputFunctor \
                                 (2* std::is_same<std::result_of_t<OutputFunctor(int)>, bool>::value)
#define DeflOutputAbortable_WindowFunctor \
                                 (2* std::is_convertible<std::decay_t<std::result_of_t<WindowFunctor(int,int)>>, int>::value)
#define DeflReturnType std::result_of_t<gunzip_ns::SizeTracker<SizeTrackTag>(int)>


#ifdef DEFLATE_ALLOCATION_DYNAMIC
# include <memory>
#endif

// RandomAccessBitArray: An engine for arrays of data items that are not byte-aligned
template<typename U = std::uint_least64_t>
struct RandomAccessBitArrayBase
{
private:
    static constexpr unsigned Ubytes = sizeof(U), Ubits = Ubytes*8;

    static std::uint_fast64_t Get_Unclean(unsigned Size, const U* data, unsigned index) throw()
    {
        unsigned bitpos = index*Size, unitpos = bitpos / Ubits, shift = bitpos % Ubits;
        std::uint_fast64_t result = data[unitpos] >> shift;
        //assert(Size <= sizeof(result)*8);
        unsigned acquired = Ubits - shift;
        for(; acquired < Size; acquired += Ubits)
        {
            result += (std::uint_fast64_t)data[++unitpos] << acquired;
        }
        return result;
    }
public:
    template<unsigned Size>
    static std::uint_fast64_t Get(const U* data, unsigned index) throw()
    {
        std::uint_fast64_t result = Get_Unclean(Size,data,index);
        return (Size >= sizeof(result)*8) ? result : (result & ((std::uint64_t(1) << Size)-1));
    }

    template<unsigned Size, bool update = false>
    static void Set(U* data, unsigned index, std::uint_fast64_t value) throw()
    {
        unsigned bitpos = index*Size, unitpos = bitpos / Ubits, eat = 0;
        // Make sure our storage unit is at least as bit as value
        //assert(Ubits >= sizeof(value)*8);
        //assert(Size >= sizeof(value)*8 || value < (std::uint64_t(1) << Size));

        if(Size % Ubits != 0)
        {
            unsigned shift = bitpos % Ubits;
            eat = Ubits - shift; if(eat > Size) eat = Size;

            //assert(eat < sizeof(std::uint_fast64_t)*8);
            //assert(shift + eat <= Ubits);
            std::uint_fast64_t vmask = (std::uint64_t(1) << eat)-1;
            if(update)
                data[unitpos] = (data[unitpos] & ~(vmask << shift)) | (value << shift);
            else
                data[unitpos] |= value << shift;
            //assert(eat < sizeof(value)*8);
            value >>= eat;
            ++unitpos;
        }
        if(eat < Size)
            for(unsigned remain = Size-eat; ; ++unitpos)
            {
                eat = Ubits;
                if(eat > remain)
                {
                    eat = remain;
                    if(update)
                    {
                        std::uint_fast64_t vmask = ((std::uint64_t(1) << eat)-1);
                        data[unitpos] = (data[unitpos] & ~vmask) | value;
                    }
                    else
                    {
                        data[unitpos] |= value;
                    }
                    break;
                }
                else
                {
                    data[unitpos] = value;
                    value >>= Ubits/2; value >>= Ubits/2;
                    remain -= Ubits;
                    if(!remain) break;
                }
            }
    }
};

template<unsigned Nbits, typename U = std::uint_least64_t>
struct RandomAccessBitArray
{
    static constexpr unsigned Ubytes = sizeof(U), Ubits = Ubytes*8, Nunits = (Nbits+Ubits-1)/Ubits;
    U data[Nunits];

    template<unsigned Size>
    inline std::uint_fast64_t Get(unsigned index) const throw()
    {
        return RandomAccessBitArrayBase<U>::template Get<Size>(data, index);
    }

    template<unsigned Size, bool update = false>
    inline void Set(unsigned index, std::uint_fast64_t value) throw()
    {
        RandomAccessBitArrayBase<U>::template Set<Size,update>(data, index, value);
    }
};

namespace gunzip_ns
{
    struct dummy{};

    // Utility: ceil(log2(n))
    template<unsigned long N> struct CeilLog2_s{ static constexpr unsigned result = 1+CeilLog2_s<(N+1)/2>::result; };
    template<> struct CeilLog2_s<0> { static constexpr unsigned result = 0; };
    template<> struct CeilLog2_s<1> { static constexpr unsigned result = 0; };
    template<unsigned long N> static constexpr unsigned CeilLog2 = CeilLog2_s<N>::result;

    // Utility: floor(log2(n))
    template<unsigned long N> struct FloorLog2_s{ static constexpr unsigned result = 1+FloorLog2_s<N/2>::result; };
    template<> struct FloorLog2_s<0> { static constexpr unsigned result = 0; };
    template<> struct FloorLog2_s<1> { static constexpr unsigned result = 0; };
    template<unsigned long N> static constexpr unsigned FloorLog2 = FloorLog2_s<N>::result;

    // Utility: smallest unsigned integer type that can store n-bit value
    template<unsigned bits>
    using SmallestType = std::conditional_t< (bits<=16),
                         std::conditional_t< (bits<= 8), std::uint_least8_t,  std::uint_least16_t>,
                         std::conditional_t< (bits<=32), std::uint_least32_t, std::uint_least64_t>>;

    // testcases
    static_assert(FloorLog2<1> == 0, "FloorLog2 fail"); static_assert(CeilLog2<1> == 0, "CeilLog2 fail");
    static_assert(FloorLog2<2> == 1, "FloorLog2 fail"); static_assert(CeilLog2<2> == 1, "CeilLog2 fail");
    static_assert(FloorLog2<3> == 1, "FloorLog2 fail"); static_assert(CeilLog2<3> == 2, "CeilLog2 fail");
    static_assert(FloorLog2<4> == 2, "FloorLog2 fail"); static_assert(CeilLog2<4> == 2, "CeilLog2 fail");
    static_assert(FloorLog2<5> == 2, "FloorLog2 fail"); static_assert(CeilLog2<5> == 3, "CeilLog2 fail");
    static_assert(FloorLog2<6> == 2, "FloorLog2 fail"); static_assert(CeilLog2<6> == 3, "CeilLog2 fail");
    static_assert(FloorLog2<7> == 2, "FloorLog2 fail"); static_assert(CeilLog2<7> == 3, "CeilLog2 fail");
    static_assert(FloorLog2<8> == 3, "FloorLog2 fail"); static_assert(CeilLog2<8> == 3, "CeilLog2 fail");
    static_assert(FloorLog2<9> == 3, "FloorLog2 fail"); static_assert(CeilLog2<9> == 4, "CeilLog2 fail");

    template<bool packed, unsigned Dimension, unsigned ElementSize>
    struct RandomAccessArray {};

    template<unsigned Dim, unsigned Elem>
    struct RandomAccessArray<true, Dim, Elem>
    {
        RandomAccessBitArray<Dim*Elem> impl;
        inline std::uint_fast64_t Get(unsigned index) const { return impl.template Get<Elem>(index); }
        inline void Set(unsigned index, std::uint_fast32_t value)  { impl.template Set<Elem,true>(index, value); }
        inline void QSet(unsigned index, std::uint_fast32_t value) { impl.template Set<Elem,false>(index, value); }
        template<unsigned Bits>
        inline void WSet(unsigned index, std::uint_fast64_t value) { impl.template Set<Bits,true>(index, value); }
    };

    template<unsigned Dim, unsigned Elem>
    struct RandomAccessArray<false, Dim, Elem>
    {
        typedef SmallestType<Elem> E;
        E data[Dim];
        inline E Get(unsigned index) const        { return data[index]; }
        inline void Set(unsigned index, E value)  { data[index] = value; }
        inline void QSet(unsigned index, E value) { data[index] = value; }
        template<unsigned Bits>
        inline void WSet(unsigned index, std::uint_fast64_t value)
        {
            index *= Bits/Elem;
            for(unsigned b=0; b<Bits; b+=Elem, value>>=Elem)
                QSet(index++, (value % (1u << Elem)));
        }
    };
}


namespace gunzip_ns
{
    template<unsigned A,unsigned B>
    void CreateHuffmanTree(const char* why,
                           RandomAccessArray<USE_BITARRAY_FOR_HUFFNODES,A,B>& tree,
                           unsigned num_values,
                           const RandomAccessArray<USE_BITARRAY_FOR_LENGTHS, 288, 4>& lengths) throw()
    {
        //#define DEFL_DO_HUFF_STATS
        constexpr unsigned ElemBits = CeilLog2<A-15>; // ceil(log2(A-15)) where A-15 is max value of num_values
        static_assert((1u << B) >= (A-15), "B is too small");
        /*assert(num_values <= C);*/

        RandomAccessArray<USE_BITARRAY_TEMPORARY_IN_HUFFMAN_CREATION, 15, ElemBits> offs; // 24 or 16 bytes.
        // Clear code length count table
        tree.template WSet<(15*B + 63) & ~63>(0, 0); // First 15 needed, but round to nice unit
        // Scan symbol length, and sum code length counts
        #ifdef DEFL_DO_HUFF_STATS
        unsigned largest_treetable_value = 0, largest_offs = 0, smallest_treetable_value = ~0u;
        unsigned largest_treetrans_index=0, largest_treetrans_value=0;
        unsigned longest_length = 0;
        #else
        why=why;
        #endif
        for(unsigned a = 0; a < num_values; ++a)
            if(std::uint_fast8_t length = lengths.Get(a)) // Note: Can be zero.
            {
                unsigned v = tree.Get(0 + length-1)+1;
            #ifdef DEFL_DO_HUFF_STATS
                largest_treetable_value = std::max(largest_treetable_value, v);
                longest_length          = std::max(longest_length, unsigned(length));
            #endif
                tree.Set(0 + length-1, v);
            }

        // Compute offset table for distribution sort
        for(unsigned sum=0, a = 1; a < 16; ++a)
        {
            offs.Set(a-1, sum);
            sum += tree.Get(0 + a-1);
        }
        #ifdef DEFL_DO_HUFF_STATS
        for(unsigned a=1; a<=longest_length; ++a)
            smallest_treetable_value = std::min(smallest_treetable_value, (unsigned)tree.Get(0 + a-1));
        #endif

        // Create code->symbol translation table (symbols sorted by code)
        for(unsigned value = 0; value < num_values; ++value)
            if(std::uint_fast8_t length = lengths.Get(value))
            {
                unsigned q = offs.Get(length-1); offs.Set(length-1, q+1); // q = offset[length]++;
        #ifdef DEFL_DO_HUFF_STATS
                largest_offs = std::max(q, largest_offs);
                largest_treetrans_index = std::max(largest_treetrans_index, q);
                largest_treetrans_value = std::max(largest_treetrans_value, value);
        #endif
                assert(q < num_values && value < num_values);
                tree.Set(15 + q, value);
            }
        #ifdef DEFL_DO_HUFF_STATS
        std::fprintf(stderr, "Largest \"%12s\"(treetable_value=%4u..%4u, offs=%4u, treetrans_index=%4u, treetrans_value=%4u)\n",
            why, smallest_treetable_value,largest_treetable_value,
            largest_offs, largest_treetrans_index, largest_treetrans_value);
        #endif

        // Largest values observed in the wild:

        // Dyn Lengths: Max treetable_value =255, max offs =285, max treetrans_index =285, max treetrans_value =285
        // Stat Lengths:Max treetable_value =152, max offs =287, max treetrans_index =287, max treetrans_value =287

        // Len Lengths: Max treetable_value = 13, max offs = 18, max treetrans_index = 18, max treetrans_value = 18
        // Dyn Dists:   Max treetable_value = 19, max offs = 29, max treetrans_index = 29, max treetrans_value = 29
        // Stat Dists:  Max treetable_value = 32, max offs = 31, max treetrans_index = 31, max treetrans_value = 31
    }

    struct DeflateState
    {
        // Lengths are in 0..15 range.
        // 144 bytes are allocated.
        RandomAccessArray<USE_BITARRAY_FOR_LENGTHS, 288, CeilLog2<16>> Lengths;

        // Length tree
        //   Values up to 288 in indexes 0-14.   (Table)  (255 is max observed in wild)
        //   Values up to 287 in indexes 15-302. (Trans)
        RandomAccessArray<USE_BITARRAY_FOR_HUFFNODES, 15+288, CeilLog2<289>> ltree;
        // Distance tree
        //   Values up to 32 in indexes 0-14.  (Table)
        //   Values up to 31 in indexes 15-46. (Trans)
        RandomAccessArray<USE_BITARRAY_FOR_HUFFNODES, 15+32, CeilLog2<33>> dtree;

        // Theoretical minimum memory use:
        //   ceil((15*log2(289) + 288*log2(288) + 15*log2(33) + 32*log2(32))/8) = 339 bytes. We use 384 bytes.
        std::uint_least8_t BitCache = 0, BitCount = 0;
        bool fixed_table = false;

        template<typename InputFunctor, bool Abortable>
        std::uint_least64_t GetBits(InputFunctor&& input, unsigned numbits)
        {
            std::uint_fast64_t result = BitCache;
            if(numbits <= BitCount)
            {
                BitCount -= numbits;
                BitCache >>= numbits;
                result &= ((1u << numbits)-1); // 0-8
                return result;
            }
            for(unsigned acquired = BitCount; ; acquired += 8)
            {
                unsigned byte = input();
                if(Abortable && (byte & ~0xFFu))
                {
                    // Note: Throws away bits already eaten from BitCache
                    return ~std::uint_least64_t(0); // error
                }
                unsigned eat = numbits-acquired;
                byte &= 0xFF;
                if(eat <= 8)
                {
                    result |= ((std::uint_fast64_t)(byte & ((1u << eat)-1))) << acquired;
                    BitCount =       8-eat;
                    BitCache = byte >> eat;
                    return result;
                }
                result |= ((std::uint_fast64_t)(byte)) << acquired;
            }
        }

        template<typename InputFunctor, bool Abortable, unsigned A,unsigned B>
        std::uint_least32_t HuffRead(InputFunctor&& input,
                                     RandomAccessArray<USE_BITARRAY_FOR_HUFFNODES,A,B>& tree)
        {
            int sum=0, cur=0, len=0;
            #ifdef DEFL_DO_HUFF_STATS
            static int maxlen = 0;
            #endif
            // Get more bits while code value is above sum
            do {
                auto p = GetBits<InputFunctor,Abortable>(std::forward<InputFunctor>(input), 1);
                if(Abortable && !~p)
                {
                    // Note: Throws away progress already made traversing the tree
                    return ~std::uint_least32_t(0); // error flag
                }
                cur = (unsigned(cur) << 1) | bool(p);
            #ifdef DEFL_DO_HUFF_STATS
                if(len > maxlen)
                {
                    maxlen = len;
                    std::fprintf(stderr, "maxlen access: %d (%d)\n", maxlen, (int)tree.Get(0 + len));
                }
            #endif
                auto v = tree.Get(0 + len++);
                sum += v;
                cur -= v;
            } while(cur >= 0);
            return tree.Get(15 + sum + cur);
        }
    };

    struct DeflateWindow
    {
        unsigned char Data[gunzip_ns::MAX_WINDOW_SIZE];
        SmallestType<CeilLog2<gunzip_ns::MAX_WINDOW_SIZE>> Head = 0;
    };

#ifdef DEFLATE_USE_DATA_TABLES
    template<bool=0> // Using a dummy template parameter makes this function and its data weak,
    inline const std::uint_least8_t* GetBTable() throw() // removing linker problems in multi-module use
    {
        static const std::uint_least8_t data[] {
            // Length bases (0-31)
            0,1,2,3,4,5,6,7,8,10,12,14,16,20,24,28,32,40,48,56,64,80,96,112,128,160,192,224,255, 0,0,0
            // Length bits and distance bits (29-60) (overlap 3 bytes)
            //               0x00,0x01,0x01,0x02,0x02,0x13,0x13,0x14,0x14,0x25,0x25,0x26,0x26,
            //0x37,0x37,0x38,0x38,0x49,0x49,0x4A,0x4A,0x5B,0x5B,0x5C,0x5C,0x0D,0x0D,0x00,0x00
        };
        return data;
    }
    template<bool=0>
    inline const std::uint_least16_t* GetWTable() throw()
    {
        static const std::uint_least16_t data[32] {
             1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577, 0,0 };
        return data;
    }

    inline unsigned dbase(unsigned distcode) { return GetWTable<>()[distcode]; }
    inline unsigned lbase(unsigned lencode)  { return GetBTable<>()[lencode-257+0] + 3; }
    //inline unsigned dbits(unsigned distcode) { return GetBTable<>()[distcode+32] & 0xF; }
    //inline unsigned lbits(unsigned lencode) { return GetBTable<>()[lencode-257+32] >> 4; }
#else
    inline unsigned dbase(unsigned distcode) { return (1 + (distcode>=4 ? ((2+distcode%2) << (distcode/2-1)) : distcode)); }
    inline unsigned lbase(unsigned lencode)  { return (lencode > 285 ? 3 : ((lencode >= 265) ? (((lencode-257)%4+4) << ((lencode-257)/4-1)) + (lencode==285 ? 2 : 3) : (lencode-254))); }
#endif
    inline unsigned dbits(unsigned distcode) { return distcode>=4 ? distcode/2-1 : 0; }
    inline unsigned lbits(unsigned lencode)  { return ((lencode>=265 && lencode<285) ? ((lencode-265)/4+1) : 0); }
    inline unsigned order(unsigned index)    { return index<3 ? (index+16) : ((index%2) ? (1-index/2)&7 : (6+index/2)); }

    template<bool Abortable>
    struct OutputHelper
    {
        template<typename OutputFunctor>
        static inline bool output(OutputFunctor&& output, unsigned char byte)
        {
            output(byte);
            return false;
        }
        template<typename WindowFunctor>
        static inline bool outputcopy(WindowFunctor&& outputcopy, std::uint_least16_t length, std::uint_fast32_t offset)
        {
            outputcopy(length, offset);
            return false;
        }
    };

    template<>
    struct OutputHelper<true>
    {
        template<typename OutputFunctor>
        static inline bool output(OutputFunctor&& output, unsigned char byte)
        {
            return output(byte);
        }
        template<typename WindowFunctor>
        static inline bool outputcopy(WindowFunctor&& outputcopy, std::uint_least16_t& length, std::uint_fast32_t offset)
        {
            length = outputcopy(length, offset);
            return length != 0;
        }
    };

    struct SizeTracker_NoOutput
    {
        inline void OutByte()                    { }
        inline void OutBytes(std::uint_fast64_t) { }

        // Dummy forwarders. Do the same as std::forward.
        template<typename T>
        static inline constexpr T&& ForwardOutput(std::remove_reference_t<T>& fun) { return static_cast<T&&>(fun); }
        template<typename T>
        static inline constexpr T&& ForwardOutput(std::remove_reference_t<T>&& fun) { return static_cast<T&&>(fun); }

        template<typename T>
        static inline constexpr T&& ForwardWindow(std::remove_reference_t<T>& fun) { return static_cast<T&&>(fun); }
        template<typename T>
        static inline constexpr T&& ForwardWindow(std::remove_reference_t<T>&& fun) { return static_cast<T&&>(fun); }
    };
    struct SizeTracker_NoInput
    {
        inline void InByte()                    { }
        inline void InBytes(std::uint_fast64_t) { }

        template<typename T>
        static inline constexpr T&& ForwardInput(std::remove_reference_t<T>& fun) { return static_cast<T&&>(fun); }
        template<typename T>
        static inline constexpr T&& ForwardInput(std::remove_reference_t<T>&& fun) { return static_cast<T&&>(fun); }
    };
    struct SizeTracker_DoInput
    {
        std::uint_fast64_t insize=0;

        inline void InByte()                      { ++insize; }
        inline void InBytes(std::uint_fast64_t n) { insize += n; }

        template<typename InputFunctor, std::enable_if_t<!DeflInputAbortable_InputFunctor,gunzip_ns::dummy>...>
        auto ForwardInput(const InputFunctor& input)
        {
            return [&]() { InByte(); return input(); };
        }

        template<typename InputFunctor, std::enable_if_t<DeflInputAbortable_InputFunctor,gunzip_ns::dummy>...>
        auto ForwardInput(const InputFunctor& input)
        {
            return [&]() { auto r = input(); if(!(r & ~0xFF)) { InByte(); } return r; };
        }
    };
    struct SizeTracker_DoOutput
    {
        std::uint_fast64_t outsize=0;

        inline void OutByte()                      { ++outsize; }
        inline void OutBytes(std::uint_fast64_t n) { outsize += n; }

        template<typename OutputFunctor, std::enable_if_t<!DeflOutputAbortable_OutputFunctor,gunzip_ns::dummy>...>
        auto ForwardOutput(const OutputFunctor& output)
        {
            return [&](unsigned char byte) { OutByte(); return output(byte); };
        }

        template<typename OutputFunctor, std::enable_if_t<DeflOutputAbortable_OutputFunctor,gunzip_ns::dummy>...>
        auto ForwardOutput(const OutputFunctor& output)
        {
            return [&](unsigned char byte) { auto r = output(byte); if(!r) { OutByte(); } return r; };
        }

        template<typename WindowFunctor, std::enable_if_t<!DeflOutputAbortable_WindowFunctor,gunzip_ns::dummy>...>
        auto ForwardWindow(const WindowFunctor& outputcopy)
        {
            return [&](std::uint_least16_t length, std::uint_fast32_t offset)
            {
                OutBytes(length);
                return outputcopy(length, offset);
            };
        }

        template<typename WindowFunctor, std::enable_if_t<DeflOutputAbortable_WindowFunctor,gunzip_ns::dummy>...>
        auto ForwardWindow(const WindowFunctor& outputcopy)
        {
            return [&](std::uint_least16_t length, std::uint_fast32_t offset)
            {
                auto remain = outputcopy(length, offset);
                OutBytes(length - remain);
                return remain;
            };
        }
    };

    template<typename TrackType>
    struct SizeTracker: public SizeTracker_NoOutput, public SizeTracker_NoInput
    {
        inline int operator() (int returncode) const { return returncode; }
    };
    template<>
    struct SizeTracker<DeflateTrackOutSize>: public SizeTracker_NoInput, public SizeTracker_DoOutput
    {
        typedef std::pair<int,std::uint_fast64_t> result;
        inline result operator() (int returncode) const { return result{returncode,outsize}; }
    };
    template<>
    struct SizeTracker<DeflateTrackInSize>: public SizeTracker_NoOutput, public SizeTracker_DoInput
    {
        typedef std::pair<int,std::uint_fast64_t> result;
        inline result operator() (int returncode) const { return result{returncode,insize}; }
    };
    template<>
    struct SizeTracker<DeflateTrackBothSize>: public SizeTracker_DoInput, public SizeTracker_DoOutput
    {
        typedef std::pair<int, std::pair<std::uint_fast64_t,std::uint_fast64_t>> result;
        inline result operator() (int returncode) const { return result{returncode,std::make_pair(insize,outsize)}; }
    };

    #ifdef DEFLATE_ALLOCATION_STATIC
    template<bool=0>
    gunzip_ns::DeflateState& GetState()
    {
        static thread_local gunzip_ns::DeflateState state;
        state.~DeflateState();
        new(&state) DeflateState();
        return state;
    }
    template<bool=0>
    gunzip_ns::DeflateWindow& GetWindow()
    {
        static thread_local gunzip_ns::DeflateWindow window;
        return window;
    }
    #endif
}//ns

/* Values of Abortable:
 *
 *   Input abortable    Output abortable   Resumable     Value
 *                no                  no          no     0
 *               yes                  no          no     1
 *                no                 yes          no     2
 *               yes                 yes          no     3
 *                                                       4 = invalid
 *               yes                  no         yes     5
 *                no                 yes         yes     6
 *               yes                 yes         yes     7
 */
template<unsigned char Abortable,
         typename InputFunctor, typename OutputFunctor, typename WindowFunctor>
int Deflate(gunzip_ns::DeflateState& state,
            InputFunctor&& input,
            OutputFunctor&& output,
            WindowFunctor&& outputcopy)
{
    using namespace gunzip_ns;

    // The following routines are macros rather than e.g. lambda functions,
    // in order to make them inlined in the function structure, and breakable/resumable.

    // Bit-by-bit input routine
    #define DummyGetBits(numbits) do { \
        auto p = state.template GetBits<InputFunctor,bool(Abortable&1)>(std::forward<InputFunctor>(input), numbits); \
        if((Abortable & 1) && !~p) return -2; \
    } while(0)

    #define GetBits(numbits, target) \
        auto p = state.template GetBits<InputFunctor,bool(Abortable&1)>(std::forward<InputFunctor>(input), numbits); \
        if((Abortable & 1) && !~p) return -2; \
        target = p

    // Huffman tree read routine.
    #define HuffRead(tree, target) \
        auto p = state.HuffRead<InputFunctor,bool(Abortable&1)>(std::forward<InputFunctor>(input), tree); \
        if((Abortable & 1) && !~p) return -2; \
        target = p

    #define Fail_If(condition) do { \
        /*assert(!(condition));*/ \
        if(condition) return -1; \
    } while(0)

    // Read stream header
    GetBits(16, std::uint_least16_t header);
    // ^ Read deflate header: method[4] ; winsize[4] ; checksum[8]
    if(header == 0x8B1F) // Is it actually a gzip header?
    {
        // Get format identifier, flags, MTIME, XFL and OS
        GetBits(64, header); Fail_If((header & 0xFF) != 8); // Format identifier should be 8
        if(header&0x0400) // Skip extra fields as indicated by FEXTRA
            { GetBits(16, std::uint_fast16_t q); DummyGetBits(8*q); }
        if(header&0x0800) for(;;) { GetBits(8, bool q); if(!q) break; } // NAME: Skip filename if FNAME was present
        if(header&0x1000) for(;;) { GetBits(8, bool q); if(!q) break; } // COMMENT: Skip comment if FCOMMENT was present
        if(header&0x0200) { DummyGetBits(16); }      // HCRC: Skip FCRC if was present
        outputcopy(0, 32768u); // GZIP always uses 32k window
    }
    else // No. Deflate header?
    {
        Fail_If((header & 0x208F) != 0x0008 || ((((header<<8)+(header>>8))&0xFFFF)%31) != 0);
        outputcopy(0, 256 << ((header >> 4) & 0xF)); // Preset dictionary (0x2000) is not supported
    }

    // Read compressed blocks
    for(;;)
    {
        GetBits(3, header);
        if(header & 4) // Dynamic block
        {
            Fail_If(header & 2);
            std::uint_least16_t nlen_ndist_ncode;
            GetBits(14, nlen_ndist_ncode);
            #define nlen  (((nlen_ndist_ncode >> 0u) & 0x1Fu) + 257u) // 257..288
            #define ndist (((nlen_ndist_ncode >> 5u) & 0x1Fu) + 1u)   // 1..32

            std::uint_least8_t ncode = ((nlen_ndist_ncode >> 10u) + 4u); // 4..19
            {std::uint_fast64_t lenlens; GetBits(ncode*3, lenlens);  // Max: 19*3 = 57 bits
            state.Lengths.template WSet<(19*4 + 63) & ~63>(0, 0);  // ncode needed, but round to nice unit
            for(unsigned a=0; a<ncode; ++a)
                state.Lengths.QSet(order(a), ((lenlens >> (a*3)) & 7));}
            CreateHuffmanTree("Len Lengths", state.dtree, 19, state.Lengths); // length-lengths. Size: 19

            if(USE_BITARRAY_FOR_LENGTHS) state.Lengths = {}; // clear at least nlen nibbles; easiest to clear it all
            std::uint_least8_t lencode = 0;
            std::uint_least16_t code = 0, remain = nlen+ndist; // nlen+ndist is 258..320
            do {
                HuffRead(state.dtree, std::uint_least8_t what); // 0-18

                if(!(what & 16))    { lencode = what * 0x11u;           what = 0x01; } // 1 times (what < 16) (use what, set prev)
                else if(what < 17)  { lencode = (lencode >> 4) * 0x11u; what = 0x23; } // 3..6 (use prev)
                else if(what == 17) { lencode &= 0xF0;                  what = 0x33; } // 3..10   (use 0)
                else                { lencode &= 0xF0;                  what = 0x7B; } // 11..138 (use 0)
                {GetBits(what >> 4, std::uint_least8_t num); num += (what & 0xF);

                Fail_If(num > remain);
                remain -= num;
                while(num--)
                {
                    if(code == nlen) // nlen is > ndist, so this is only matched once
                    {
                        CreateHuffmanTree("Dyn Lengths", state.ltree, nlen, state.Lengths);  // size: 257..288
                        if(USE_BITARRAY_FOR_LENGTHS)
                            state.Lengths.template WSet<(32*4 + 63) & ~63>(0,0); // ndist needed, but round to nice unit
                        code = 0;
                    }
                    state.Lengths.QSet(code++, lencode & 0xF);
                }}
            } while(remain > 0);
            CreateHuffmanTree("Dyn Dists", state.dtree, ndist, state.Lengths); // size: 1..32
            state.fixed_table = false;
            #undef nlen
            #undef ndist
        }
        else           // Fixed block
        {
            if(header < 2) // Copy stored block data
            {
                DummyGetBits(state.BitCount%8); // Go to byte boundary (discard a few bits)
                GetBits(32, std::uint_least32_t a);
                Fail_If(((a ^ (a >> 16)) & 0xFFFF) != 0xFFFF);
                // Note: It is valid for (lower 16 bits of) "a" to be 0 here.
                // It is sometimes used for aligning the stream to byte boundary.
                while(a-- & 0xFFFF)
                {
                    GetBits(8, unsigned char octet);
                    while(OutputHelper<bool(Abortable&2)>::output(output, octet)) { return -3; }
                }
                goto skipdef;
            }
            if(!state.fixed_table)
            {
                for(unsigned n=0; n<9; ++n) state.Lengths.template WSet<64>((n*16+0)/16,    0x8888888888888888ull);
                for(unsigned n=0; n<7; ++n) state.Lengths.template WSet<64>((n*16+0x90)/16, 0x9999999999999999ull);
                for(unsigned n=0; n<4; ++n) state.Lengths.template WSet<32>((n*8+0x100)/8,  (7+n/3)*0x11111111u);

                CreateHuffmanTree("Stat Lengths", state.ltree, 288, state.Lengths);

                for(unsigned n=0; n<2; ++n) state.Lengths.template WSet<64>((n*16+0)/16,    0x5555555555555555ull);

                CreateHuffmanTree("Stat Dists", state.dtree, 32, state.Lengths);
                state.fixed_table = true;
            }
        }
        // Do actual deflating.
        for(;;)
        {
            HuffRead(state.ltree, std::uint_least16_t lencode); // 0..287
            if(!(lencode & -256)) // 0..255: literal byte
            {
                while(OutputHelper<bool(Abortable&2)>::output(output, lencode)) { return -3; }
            }
            else if(!(lencode & 0xFF)) break; // 256=end
            else // 257..287: length code for backwards reference
            {
                GetBits(lbits(lencode), std::uint_least16_t length); length += lbase(lencode);
                {HuffRead(state.dtree, std::uint_least8_t distcode); // Read distance code (0..31)
                {GetBits(dbits(distcode), std::uint_least32_t offset); offset += dbase(distcode);
                while(OutputHelper<bool(Abortable&2)>::outputcopy(outputcopy,length,offset)) { return -4; }}}
            }
        }
skipdef:if(header & 1) break; // last block flag
    }
    // Note: after this, may come a checksum, and a trailer. Ignoring them.
    #undef GetBits
    #undef DummyGetBits
    #undef Fail_If
    #undef HuffRead
    return 0;
}

/* The functor base with window functor */
template<typename InputFunctor, typename OutputFunctor, typename WindowFunctor, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputFunctor && DeflIsOutputFunctor && DeflIsWindowFunctor && DeflIsTrackTag, DeflReturnType>
    Deflate(InputFunctor&& input, OutputFunctor&& output, WindowFunctor&& outputcopy, SizeTrackTag = {})
{
#ifdef DEFLATE_ALLOCATION_AUTOMATIC
    gunzip_ns::DeflateState state;
#elif defined(DEFLATE_ALLOCATION_STATIC)
    auto& state = gunzip_ns::GetState<>();
#elif defined(DEFLATE_ALLOCATION_DYNAMIC)
    std::unique_ptr<gunzip_ns::DeflateState> stateptr(new gunzip_ns::DeflateState);
    auto& state = *stateptr;
#endif

    gunzip_ns::SizeTracker<SizeTrackTag> tracker;

    // For output to be abortable, both the output functor and window functor must have return types.
    constexpr unsigned char Abortable = DeflInputAbortable_InputFunctor
                                      | (DeflOutputAbortable_OutputFunctor & DeflOutputAbortable_WindowFunctor);

    return tracker(Deflate<Abortable>(state, tracker.template ForwardInput<InputFunctor>(input),
                                             tracker.template ForwardOutput<OutputFunctor>(output),
                                             tracker.template ForwardWindow<WindowFunctor>(outputcopy)));
}

/* The functor base without window functor */
template<typename InputFunctor, typename OutputFunctor, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputFunctor && DeflIsOutputFunctor && DeflIsTrackTag, DeflReturnType>
    Deflate(InputFunctor&& input, OutputFunctor&& output, SizeTrackTag = {})
{
    // Using a library-supplied output window. OutputFunctor will be wrapped.
#ifdef DEFLATE_ALLOCATION_AUTOMATIC
    gunzip_ns::DeflateState state;
    gunzip_ns::DeflateWindow window;
#elif defined(DEFLATE_ALLOCATION_STATIC)
    auto& state  = gunzip_ns::GetState<>();
    auto& window = gunzip_ns::GetWindow<>();
#elif defined(DEFLATE_ALLOCATION_DYNAMIC)
    std::unique_ptr<std::pair<gunzip_ns::DeflateState, gunzip_ns::DeflateWindow>> dataptr
        (new std::pair<gunzip_ns::DeflateState, gunzip_ns::DeflateWindow>);
    auto& state  = dataptr->first;
    auto& window = dataptr->second;
#endif
    gunzip_ns::SizeTracker<SizeTrackTag> tracker;

    constexpr unsigned char Abortable = DeflInputAbortable_InputFunctor
                                      | DeflOutputAbortable_OutputFunctor;
    auto Put = [&, out = tracker.template ForwardOutput<OutputFunctor>(output)](unsigned char l)
    {
        window.Data[window.Head++ % gunzip_ns::MAX_WINDOW_SIZE] = l;
        return out(l);
    };

    return tracker(Deflate<Abortable> (state,
        tracker.template ForwardInput<InputFunctor>(input),
        Put,
        [&](std::uint_least16_t length, std::uint_fast32_t offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length>0; --length)
            {
                unsigned char byte = window.Data[(window.Head - offs) % gunzip_ns::MAX_WINDOW_SIZE];
                if(gunzip_ns::OutputHelper<bool(Abortable&2)>::output(Put, byte))
                    break;
            }
            return length;
        }));
}


template<typename InputFunctor, typename OutputIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputFunctor && DeflIsOutputIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(InputFunctor&& input, OutputIterator&& target, SizeTrackTag = {})
{
    return Deflate(
        std::forward<InputFunctor>(input),
        [&](unsigned char l) { *target = l; ++target; }, SizeTrackTag{});
}


template<typename InputFunctor, typename RandomAccessIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputFunctor && DeflIsRandomAccessIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(InputFunctor&& input, RandomAccessIterator&& target, SizeTrackTag = {})
{
    return Deflate(
        std::forward<InputFunctor>(input),
        [&](unsigned char l) { *target = l; ++target; },
        [&](std::uint_least16_t length, std::uint_fast32_t offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length--; ++target) { *target = *(target-offs); }
        }, SizeTrackTag{});
}


template<typename InputFunctor, typename RandomAccessIterator, typename SizeType, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputFunctor && DeflIsRandomAccessIterator && DeflIsSizeType && DeflIsTrackTag, DeflReturnType>
    Deflate(InputFunctor&& input, RandomAccessIterator&& target, SizeType&& target_limit, SizeTrackTag = {})
{
    typename std::iterator_traits<std::decay_t<RandomAccessIterator>>::difference_type used{}, cap=target_limit;
    // Using a window functor, not a separate window.
    return Deflate(
        std::forward<InputFunctor>(input),
        [&](unsigned char l)
        {
            if(used >= cap) return true;
            target[used] = l; ++used;
            return false;
        },
        [&](std::uint_least16_t length, std::uint_fast32_t offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length > 0 && used < cap; ++used, --length)
            {
                target[used] = target[used - offs];
            }
            return length;
        }, SizeTrackTag{});
}

template<typename InputFunctor, typename RandomAccessIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputFunctor && DeflIsRandomAccessIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(InputFunctor&& input, RandomAccessIterator&& target_begin, RandomAccessIterator&& target_end, SizeTrackTag = {})
{
    // Using a window functor, not a separate window.
    return Deflate(
        std::forward<InputFunctor>(input),
        [&](unsigned char l)
        {
            if(target_begin == target_end) return true;
            *target_begin = l; ++target_begin;
            return false;
        },
        [&](std::uint_least16_t length, std::uint_fast32_t offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length > 0 && !(target_begin == target_end); --length, ++target_begin)
            {
                *target_begin = *(target_begin - offs);
            }
            return length;
        }, SizeTrackTag{});
}


/**** The same six, but with InputIterator converted into InputFunctor *****/

#define DeflInf [&]() { auto r = *input; ++input; return r; }

template<typename InputIterator, typename OutputFunctor, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsOutputFunctor && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& input, OutputFunctor&& output, SizeTrackTag = {})
{
    return Deflate(DeflInf, std::forward<OutputFunctor>(output), SizeTrackTag{});
}
template<typename InputIterator, typename OutputFunctor, typename WindowFunctor, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsOutputFunctor && DeflIsWindowFunctor && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& input, OutputFunctor&& output, WindowFunctor&& outputcopy, SizeTrackTag = {})
{
    return Deflate(DeflInf,
                   std::forward<OutputFunctor>(output),
                   std::forward<WindowFunctor>(outputcopy), SizeTrackTag{});
}
template<typename InputIterator, typename OutputIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsOutputIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& input, OutputIterator&& output, SizeTrackTag = {})
{
    return Deflate(DeflInf, std::forward<OutputIterator>(output), SizeTrackTag{});
}
template<typename InputIterator, typename RandomAccessIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsRandomAccessIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& input, RandomAccessIterator&& target, SizeTrackTag = {})
{
    return Deflate(DeflInf, std::forward<RandomAccessIterator>(target), SizeTrackTag{});
}
template<typename InputIterator, typename RandomAccessIterator, typename SizeType, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsRandomAccessIterator && DeflIsSizeType && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& input, RandomAccessIterator&& target, SizeType&& target_limit, SizeTrackTag = {})
{
    return Deflate(DeflInf, std::forward<RandomAccessIterator>(target),
                   std::forward<SizeType>(target_limit), SizeTrackTag{});
}
template<typename InputIterator, typename RandomAccessIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsRandomAccessIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& input, RandomAccessIterator&& target_begin, RandomAccessIterator&& target_end, SizeTrackTag = {})
{
    return Deflate(DeflInf, std::forward<RandomAccessIterator>(target_begin),
                   std::forward<RandomAccessIterator>(target_end), SizeTrackTag{});
}

#undef DeflInf





/**** The same six, but with two ForwardIterators converted into InputFunctor *****/
/* All this repetition hurts me, but there is no way to combine
 * enable_if, auto return type, and parameter packs. At least I couldn't find any.
 */

#define DeflInf [&]() { if(begin==end) { return -1; } auto r = *begin; ++begin; return r; }

template<typename ForwardIterator, typename OutputFunctor, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsForwardIterator && DeflIsOutputFunctor && DeflIsTrackTag, DeflReturnType>
    Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputFunctor&& output, SizeTrackTag = {})
{
    return Deflate(DeflInf,
                   std::forward<OutputFunctor>(output), SizeTrackTag{});
}
template<typename ForwardIterator, typename OutputFunctor, typename WindowFunctor, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsForwardIterator && DeflIsOutputFunctor && DeflIsWindowFunctor && DeflIsTrackTag, DeflReturnType>
    Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputFunctor&& output, WindowFunctor&& outputcopy, SizeTrackTag = {})
{
    return Deflate(DeflInf,
                   std::forward<OutputFunctor>(output),
                   std::forward<WindowFunctor>(outputcopy), SizeTrackTag{});
}
template<typename ForwardIterator, typename OutputIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsForwardIterator && DeflIsOutputIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputIterator&& output, SizeTrackTag = {})
{
    return Deflate(DeflInf,
                   std::forward<OutputIterator>(output), SizeTrackTag{});
}
template<typename ForwardIterator, typename RandomAccessIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsForwardIterator && DeflIsRandomAccessIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(ForwardIterator&& begin, ForwardIterator&& end, RandomAccessIterator&& target, SizeTrackTag = {})
{
    return Deflate(DeflInf,
                   std::forward<RandomAccessIterator>(target), SizeTrackTag{});
}
template<typename ForwardIterator, typename RandomAccessIterator, typename SizeType, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsForwardIterator && DeflIsRandomAccessIterator && DeflIsSizeType && DeflIsTrackTag, DeflReturnType>
    Deflate(ForwardIterator&& begin, ForwardIterator&& end, RandomAccessIterator&& target, SizeType&& target_limit, SizeTrackTag = {})
{
    return Deflate(DeflInf,
                   std::forward<RandomAccessIterator>(target),
                   std::forward<SizeType>(target_limit), SizeTrackTag{});
}
template<typename ForwardIterator, typename RandomAccessIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsForwardIterator && DeflIsRandomAccessIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(ForwardIterator&& begin, ForwardIterator&& end, RandomAccessIterator&& target_begin, RandomAccessIterator&& target_end, SizeTrackTag = {})
{
    return Deflate(DeflInf,
                   std::forward<RandomAccessIterator>(target_begin),
                   std::forward<RandomAccessIterator>(target_end), SizeTrackTag{});
}

#undef DeflInf



/**** The same six, but with an InputIterator and a length, converted into InputFunctor *****/

#define DeflInit typename std::iterator_traits<std::decay_t<InputIterator>>::difference_type remain(length)
#define DeflInf [&]() -> std::common_type_t<int, decltype(*begin)> \
                { if(!remain) { return -1; } --remain; auto r = *begin; ++begin; return r; }

template<typename InputIterator, typename SizeType, typename OutputFunctor, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsSizeType && DeflIsOutputFunctor && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& begin, SizeType&& length, OutputFunctor&& output, SizeTrackTag = {})
{
    DeflInit;
    return Deflate(DeflInf,
                   std::forward<OutputFunctor>(output), SizeTrackTag{});
}
template<typename InputIterator, typename SizeType, typename OutputFunctor, typename WindowFunctor, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsSizeType && DeflIsOutputFunctor && DeflIsWindowFunctor && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& begin, SizeType&& length, OutputFunctor&& output, WindowFunctor&& outputcopy, SizeTrackTag = {})
{
    DeflInit;
    return Deflate(DeflInf,
                   std::forward<OutputFunctor>(output),
                   std::forward<WindowFunctor>(outputcopy), SizeTrackTag{});
}
template<typename InputIterator, typename SizeType, typename OutputIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsSizeType && DeflIsOutputIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& begin, SizeType&& length, OutputIterator&& output, SizeTrackTag = {})
{
    DeflInit;
    return Deflate(DeflInf,
                   std::forward<OutputIterator>(output), SizeTrackTag{});
}
template<typename InputIterator, typename SizeType, typename RandomAccessIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsSizeType && DeflIsRandomAccessIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& begin, SizeType&& length, RandomAccessIterator&& target, SizeTrackTag = {})
{
    DeflInit;
    return Deflate(DeflInf,
                   std::forward<RandomAccessIterator>(target), SizeTrackTag{});
}
template<typename InputIterator, typename SizeType, typename RandomAccessIterator, typename SizeType2, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsSizeType && DeflIsRandomAccessIterator && DeflIsSizeType2 && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& begin, SizeType&& length, RandomAccessIterator&& target, SizeType2&& target_limit, SizeTrackTag = {})
{
    DeflInit;
    return Deflate(DeflInf,
                   std::forward<RandomAccessIterator>(target),
                   std::forward<SizeType2>(target_limit), SizeTrackTag{});
}
template<typename InputIterator, typename SizeType, typename RandomAccessIterator, typename SizeTrackTag = DeflateTrackNoSize>
std::enable_if_t<DeflIsInputIterator && DeflIsSizeType && DeflIsRandomAccessIterator && DeflIsTrackTag, DeflReturnType>
    Deflate(InputIterator&& begin, SizeType&& length, RandomAccessIterator&& target_begin, RandomAccessIterator&& target_end, SizeTrackTag = {})
{
    DeflInit;
    return Deflate(DeflInf,
                   std::forward<RandomAccessIterator>(target_begin),
                   std::forward<RandomAccessIterator>(target_end), SizeTrackTag{});
}

#undef DeflInf
#undef DeflInit




#undef DeflIsWindowFunctor
#undef DeflIsInputFunctor
#undef DeflIsWindowFunctor
#undef DeflIsRandomAccessIterator
#undef DeflIsForwardIterator
#undef DeflIsInputIterator
#undef DeflIsOutputIterator
#undef DeflIsSizeType
#undef DeflIsSizeType2
#undef DeflInputAbortable_InputFunctor
#undef DeflOutputAbortable_OutputFunctor
#undef DeflOutputAbortable_WindowFunctor
#undef DeflReturnType
