/* My tiny gzip decompressor without using zlib. - Joel Yliluoma
 * http://iki.fi/bisqwit/ , http://youtube.com/user/Bisqwit
 * Inspired and influenced by a 13th IOCCC winner program by Ron McFarland */
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
//       1 = input functor returned a value outside 0x00..0xFF range
//       2 = output functor returned nonzero / bool true value
//       3 = outputcopy functor returned nonzero remaining length value
//
template<typename InputFunctor, typename OutputFunctor, typename WindowFunctor>
int Deflate(InputFunctor&& input, OutputFunctor&& output, WindowFunctor&& outputcopy);

// Check README.md for the full list of versions of Deflate() available.

#endif


// The rest of the file is just for the curious about implementation.
namespace gunzip_ns
{
    // If you want more performance at the expense of RAM use,
    // Turn one or more of these settings to false:
    static constexpr bool USE_BITARRAY_TEMPORARY_IN_HUFFMAN_CREATION = true; /* 12 bytes save */
    static constexpr bool USE_BITARRAY_FOR_LENGTHS = true;                   /* 160 bytes save */
    static constexpr bool USE_BITARRAY_FOR_HUFFNODES = true;                 /* 392 bytes save */
    #define DEFLATE_USE_DATA_TABLES
}

// RandomAccessBitArray: An engine for arrays of data items that are smaller than a byte
template<typename U = std::uint_least64_t>
struct RandomAccessBitArrayBase
{
    static constexpr unsigned Ubytes = sizeof(U), Ubits = Ubytes*8;

    template<unsigned Size>
    static std::uint_fast64_t Get(const U* data, unsigned index)
    {
        unsigned bitpos = index*Size, unitpos = bitpos / Ubits, shift = bitpos % Ubits;
        std::uint_fast64_t result = data[unitpos] >> shift;
        assert(Size <= sizeof(result)*8);
        unsigned acquired = Ubits - shift;
        for(; acquired < Size; acquired += Ubits)
        {
            result += (std::uint_fast64_t)data[++unitpos] << acquired;
        }
        return (Size >= sizeof(result)*8) ? result : (result & ((std::uint64_t(1) << Size)-1));
    }

    template<unsigned Size, bool update = false>
    static void Set(U* data, unsigned index, std::uint_fast64_t value)
    {
        unsigned bitpos = index*Size, unitpos = bitpos / Ubits, eat = 0;
        // Make sure our storage unit is at least as bit as value
        assert(Ubits >= sizeof(value)*8);
        //assert(Size >= sizeof(value)*8 || value < (std::uint64_t(1) << Size));

        if(Size % Ubits != 0)
        {
            unsigned shift = bitpos % Ubits;
            eat = Ubits - shift; if(eat > Size) eat = Size;

            assert(eat < sizeof(std::uint_fast64_t)*8);
            assert(shift + eat <= Ubits);
            std::uint_fast64_t vmask = (std::uint64_t(1) << eat)-1;
            if(update)
                data[unitpos] = (data[unitpos] & ~(vmask << shift)) | (value << shift);
            else
                data[unitpos] |= value << shift;
            assert(eat < sizeof(value)*8);
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
    inline std::uint_fast64_t Get(unsigned index) const
    {
        return RandomAccessBitArrayBase<U>::template Get<Size>(data, index);
    }

    template<unsigned Size, bool update = false>
    inline void Set(unsigned index, std::uint_fast64_t value)
    {
        RandomAccessBitArrayBase<U>::template Set<Size,update>(data, index, value);
    }
};

namespace gunzip_ns
{
    template<unsigned bits>
    using SmallestType = std::conditional_t< (bits<=16),
                         std::conditional_t< (bits<= 8), std::uint_least8_t,  std::uint_least16_t>,
                         std::conditional_t< (bits<=32), std::uint_least32_t, std::uint_least64_t>>;

    template<bool packed, unsigned Dimension, unsigned ElementSize>
    struct RandomAccessArray {};

    template<unsigned Dim, unsigned Elem>
    struct RandomAccessArray<true, Dim, Elem>
    {
        RandomAccessBitArray<Dim*Elem> impl;
        inline std::uint_fast64_t Get(unsigned index) const { return impl.template Get<Elem>(index); }
        inline void Set(unsigned index, std::uint_fast32_t value) { impl.template Set<Elem,true>(index, value); }
        inline void QSet(unsigned index, std::uint_fast32_t value) { impl.template Set<Elem,false>(index, value); }
        template<unsigned Bits>
        inline void WSet(unsigned index, std::uint_fast64_t value) { impl.template Set<Bits,false>(index, value); }
    };

    template<unsigned Dim, unsigned Elem>
    struct RandomAccessArray<false, Dim, Elem>
    {
        typedef SmallestType<Elem> E;
        E data[Dim];
        inline E Get(unsigned index) const       { return data[index]; }
        inline void Set(unsigned index, E value) { data[index] = value; }
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
    static constexpr unsigned HuffNodeBits = USE_BITARRAY_FOR_HUFFNODES ? 27 : 32;
    static constexpr unsigned PoolSize     = 638;
    // Branches are in 0..637 range (number of pool indexes). --> 9.32 bits needed
    // Values are in 0..287 range.                            --> 8.17 bits needed
    // Minimum theoretically possible is 26.805 bits. 27 is pretty good.
    static_assert(!USE_BITARRAY_FOR_HUFFNODES || PoolSize*PoolSize*288 <= (1 << HuffNodeBits),     "Too few HuffNodeBits");
    static_assert(!USE_BITARRAY_FOR_HUFFNODES || PoolSize*PoolSize*288  > (1 << (HuffNodeBits-1)), "Too many HuffNodeBits");
    template<unsigned HuffNodeBits>
    struct huffnode
    {
        SmallestType<HuffNodeBits> intval; // Any integer type at least HuffNodeBits bits wide
        static_assert(sizeof(intval)*8 >= HuffNodeBits, "intval is too small");
        static constexpr unsigned BranchMul1 = USE_BITARRAY_FOR_HUFFNODES ? 640 : 1024;
        static constexpr unsigned BranchMul2 = USE_BITARRAY_FOR_HUFFNODES ? 640 : 1024;
        // BranchMul1 and BranchMul2  are arbitrary numbers both >= PoolSize
        // where log2(637 + BranchMul1*(637 + 287*BranchMul2)) < HuffNodeBits.
        // They are chosen to make fastest assembler code for the functions below.
        unsigned GetBranch0() const { return intval % BranchMul1; }
        unsigned GetBranch1() const { return (intval / BranchMul1) % BranchMul2; }
        unsigned GetValue()   const { return (intval / (BranchMul1 * BranchMul2)); }
        huffnode SetBranch0(unsigned b) { /*assert(b < PoolSize);*/ return {intval += (b - GetBranch0())}; }
        huffnode SetBranch1(unsigned b) { /*assert(b < PoolSize);*/ return {intval += (b - GetBranch1()) * (BranchMul1)}; }
        huffnode SetValue(unsigned b)   { /*assert(b < 288);*/      return {intval += (b - GetValue()) * (BranchMul1*BranchMul2)}; }
        static_assert(BranchMul1 >= PoolSize && BranchMul2 >= PoolSize
            && (PoolSize-1) + BranchMul1*((PoolSize-1) + 287*BranchMul2) < (std::uint64_t(1) << HuffNodeBits), "Illegal BranchMul values");
    };
    template<unsigned HuffNodeBits>
    struct hufftree
    {
        using nodetype = huffnode<HuffNodeBits>;
        RandomAccessArray<USE_BITARRAY_FOR_HUFFNODES,PoolSize,HuffNodeBits>& storage;
        std::uint_least16_t used    : 12; // Index of the next unused node in the pool
        std::uint_least16_t branch0 : 10;
        std::uint_least16_t branch1 : 10;

        nodetype get(std::uint_fast16_t n) const          { return { SmallestType<HuffNodeBits>(storage.Get(n-1)) }; }
        void     put(std::uint_fast16_t n, nodetype node) { storage.Set(n-1, node.intval); }

        // Create a huffman tree for num_values, with given lengths.
        // The tree will be put in branch[which]; other branch not touched.
        // Length = how many bits to use for encoding this value.
        // num_values <= 288.
        // Theoretical size limits: count[] : 0-288 (9 bits * 16)                       = 18 bytes
        //                          offs[] : theoretically max. 28310976 (25 bits * 16) = 50 bytes
        void Create(unsigned which, unsigned num_values,
                    const RandomAccessArray<USE_BITARRAY_FOR_LENGTHS, 288+32, 4>& lengths, unsigned offset)
        {
            if(!which) { used=0; branch0=0; branch1=0; }
            constexpr unsigned ElemBits = 24, OffsOffset = 0, CountOffset = 1;
            RandomAccessArray<USE_BITARRAY_TEMPORARY_IN_HUFFMAN_CREATION, 17, ElemBits> data{}; // 51 bytes.

            for(unsigned a = 0; a < num_values; ++a)
            {
                std::uint_fast8_t len = lengths.Get(offset+a); // Note: Can be zero.
                data.Set(len+CountOffset, data.Get(len+CountOffset) + 1); // increase count
            }
            for(unsigned a = 0; a < 15; a++)
                data.Set(a+1+OffsOffset,
                         2u * (data.Get(a+OffsOffset) + data.Get(a+CountOffset)));
            // Largest values seen in wild for offs[16]: 16777216
            for(unsigned value = 0; value < num_values; ++value)
                if(std::uint_fast8_t length = lengths.Get(offset+value))
                {
                    nodetype node;
                    std::uint_fast16_t b = which ? branch1 : branch0;
                    if(b) { node = get(b); }
                    else  { if(which) {branch1 = used+1;} else {branch0 = used+1;} put(b = ++used, node = {0}); }

                    std::uint_least32_t q = data.Get(length+OffsOffset); data.Set(length+OffsOffset, q+1); // q = offset[length]++
                    for(q <<= (32u-length); length--; )
                    {
                        bool bit = q >> 31; q <<= 1;
                        std::uint_fast16_t nextb = bit ? node.GetBranch1() : node.GetBranch0();
                        if(nextb)  { node = get(b = nextb); }
                        else       { put(b, bit ? node.SetBranch1(used+1) : node.SetBranch0(used+1));
                                     put(b = ++used, node = {0}); }
                    }
                    put(b, node.SetValue(value));
                }
        }
    };

    template<bool WithWindow>
    struct DeflateState
    {
        RandomAccessArray<USE_BITARRAY_FOR_LENGTHS, 288+32, 4> Lengths; // Lengths are in 0..15 range. 160 bytes are allocated.
        RandomAccessArray<USE_BITARRAY_FOR_HUFFNODES, PoolSize, HuffNodeBits> pool; // Total: 638 huffnodes (2160 bytes)
        hufftree<HuffNodeBits> tables_fixed{pool, 0,0,0}, tables_dyn{pool, 0,0,0}, *cur_table=nullptr;
        std::uint_least8_t BitCache = 0, BitCount = 0;

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

        template<typename InputFunctor, bool Abortable>
        std::uint_least32_t HuffRead(InputFunctor&& input, hufftree<HuffNodeBits>& tree, bool which)
        {
            huffnode<HuffNodeBits> tmpnode = tree.get(which ? tree.branch1 : tree.branch0);
            while(tmpnode.GetBranch1())
            {
                auto p = GetBits<InputFunctor,Abortable>(std::forward<InputFunctor>(input), 1);
                if(Abortable && !~p)
                {
                    // Note: Throws away progress already made traversing the tree
                    return ~std::uint_least32_t(0); // error flag
                }
                tmpnode = tree.get(p ? tmpnode.GetBranch1() : tmpnode.GetBranch0());
            }
            return tmpnode.GetValue();
        }
    };

#ifdef DEFLATE_USE_DATA_TABLES
    template<bool=0> // Using a dummy template parameter makes this function and its data weak,
    inline const std::uint_least8_t* GetBTable() // removing linker problems in multi-module use
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
    inline const std::uint_least16_t* GetWTable()
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
    inline unsigned lbits(unsigned lencode)  { return ((lencode>=265 && lencode<285) ? ((lencode-257)/4-1) : 0); }
    inline unsigned order(unsigned index)    { return index<3 ? (index+16) : ((index%2) ? (1-index/2)&7 : (6+index/2)); }

    template<>
    struct DeflateState<true>: public DeflateState<false>
    {
        struct { unsigned char Data[32768u]; std::uint_least16_t Head=0; } Window;
    };

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
int Deflate(gunzip_ns::DeflateState<false>& state,
            InputFunctor&& input,
            OutputFunctor&& output,
            WindowFunctor&& outputcopy)
{
    // Return values: -1 = error in input data
    //                 0 = decompression complete
    //                 1 = input()      returned non-byte
    //                 2 = outputcopy() returned nonzero (only if Abortable >= 1)
    //                 3 = output()     returned true (only if Abortable >= 1)
    using namespace gunzip_ns;

    // The following routines are macros rather than e.g. lambda functions,
    // in order to make them inlined in the function structure, and breakable/resumable.

    // Bit-by-bit input routine
    #define DummyGetBits(numbits) do { \
        auto p = state.template GetBits<InputFunctor,Abortable&1>(std::forward<InputFunctor>(input), numbits); \
        if((Abortable & 1) && !~p) return 1; \
    } while(0)

    #define GetBits(numbits, target) \
        auto p = state.template GetBits<InputFunctor,Abortable&1>(std::forward<InputFunctor>(input), numbits); \
        if((Abortable & 1) && !~p) return 1; \
        target = p

    // Huffman tree read routine.
    #define HuffRead(tree, which, target) \
        auto p = state.HuffRead<InputFunctor,Abortable&1>(std::forward<InputFunctor>(input), tree, which); \
        if((Abortable & 1) && !~p) return 1; \
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

            {state.Lengths.template WSet<32*4>(0, 0); // 19 needed, but round to nice unit
            std::uint_least8_t ncode = ((nlen_ndist_ncode >> 10u) + 4u); // 4..19
            std::uint_fast64_t lenlens; GetBits(ncode*3, lenlens);  // Max: 19*3 = 57 bits
            for(unsigned a=0; a < ncode; ++a)
                state.Lengths.QSet(order(a), ((lenlens >> (a*3)) & 7));}
            state.tables_dyn.Create(0, 19, state.Lengths, 0); // length-lengths

            state.Lengths = {}; // clear at least (nlen+ndist) nibbles; easiest to clear it all
            //state.Lengths.Set<(288+32)*4,true>(0,0);
            std::uint_least8_t lencode = 0;
            for(std::uint_least16_t code = 0; code < nlen+ndist; ) // nlen+ndist is 258..320
            {
                HuffRead(state.tables_dyn, 0, std::uint_least8_t what); // 0-18

                if(!(what & 16))    { lencode = what * 0x11u;           what = 0x01; } // 1 times (what < 16) (use what, set prev)
                else if(what < 17)  { lencode = (lencode >> 4) * 0x11u; what = 0x23; } // 3..6 (use prev)
                else if(what == 17) { lencode &= 0xF0;                  what = 0x33; } // 3..10   (use 0)
                else                { lencode &= 0xF0;                  what = 0x7B; } // 11..138 (use 0)
                {GetBits(what >> 4, std::uint_least8_t num); num += (what & 0xF);

                Fail_If((code+num) > (nlen+ndist));
                while(num--) { state.Lengths.QSet(code++, lencode & 0xF); }}
            }
            state.tables_dyn.Create(0, nlen,  state.Lengths, 0);
            state.tables_dyn.Create(1, ndist, state.Lengths, nlen);
            assert(state.tables_dyn.used <= PoolSize);
            // ^If this assertion fails, simply increase PoolSize.
            // So far the largest value seen in the wild is 630.

            //fprintf(stderr, "pool2 size%5u\n", state.tables_dyn.used);
            state.cur_table = &state.tables_dyn;
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
                    while(OutputHelper<Abortable&2>::output(output, octet)) { return 2; }
                }
                goto skipdef;
            }
            if(state.cur_table != &state.tables_fixed)
            {
                for(unsigned n=0; n<9; ++n) state.Lengths.template WSet<64>((n*16+0)/16,    0x8888888888888888ull);
                for(unsigned n=0; n<7; ++n) state.Lengths.template WSet<64>((n*16+0x90)/16, 0x9999999999999999ull);
                for(unsigned n=0; n<4; ++n) state.Lengths.template WSet<32>((n*8+0x100)/8,  (7+n/3)*0x11111111u);
                for(unsigned n=0; n<2; ++n) state.Lengths.template WSet<64>((n*16+0x120)/16,0x5555555555555555ull);
                state.tables_fixed.Create(0, 288, state.Lengths, 0);   // 575 used here
                state.tables_fixed.Create(1, 32,  state.Lengths, 288); // 63 used here
                assert(state.tables_fixed.used == 638 && state.tables_fixed.used <= PoolSize);
                // ^state.tables_fixed has always 638 elements. If this assertion fails,
                // something is wrong. Maybe coincidentally same as (288+32-1)*2.
                state.cur_table = &state.tables_fixed;
            }
        }
        // Do actual deflating.
        for(;;)
        {
            HuffRead(*state.cur_table, 0, std::uint_least16_t lencode); // 0..287
            if(!(lencode & -256)) // 0..255: literal byte
            {
                while(OutputHelper<Abortable&2>::output(output, lencode)) { return 2; }
            }
            else if(!(lencode & 0xFF)) break; // 256=end
            else // 257..287: length code for backwards reference
            {
                GetBits(lbits(lencode), std::uint_least16_t length);
                {HuffRead(*state.cur_table, 1, std::uint_least8_t distcode); // Read distance code (0..31)
                {GetBits(dbits(distcode), std::uint_least32_t offset);
                while(OutputHelper<Abortable&2>::outputcopy(
                    outputcopy,
                    length + lbase(lencode),
                    offset + dbase(distcode))) { return 3; }}}
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

#define DeflIsInputFunctor         (std::is_convertible<std::result_of_t<InputFunctor()>,int>::value)
#define DeflIsOutputFunctor        (std::is_same<std::result_of_t<OutputFunctor(int)>,void>::value|1)
#define DeflIsWindowFunctor        (std::is_same<std::result_of_t<WindowFunctor(int,int)>,void>::value|1)

#define DeflIsForwardIterator      (std::is_convertible<decltype(*std::decay_t<ForwardIterator>()), int>::value \
                                    && (std::is_same<typename std::iterator_traits<std::decay_t<ForwardIterator>>::iterator_category, std::forward_iterator_tag>::value \
                                     || std::is_same<typename std::iterator_traits<std::decay_t<ForwardIterator>>::iterator_category, std::bidirectional_iterator_tag>::value \
                                     || std::is_same<typename std::iterator_traits<std::decay_t<ForwardIterator>>::iterator_category, std::random_access_iterator_tag>::value))

#define DeflIsInputIterator        (std::is_convertible<decltype(*std::decay_t<InputIterator>()), int>::value \
                                    && (std::is_same<typename std::iterator_traits<std::decay_t<InputIterator>>::iterator_category, std::input_iterator_tag>::value \
                                     || std::is_same<typename std::iterator_traits<std::decay_t<InputIterator>>::iterator_category, std::forward_iterator_tag>::value \
                                     || std::is_same<typename std::iterator_traits<std::decay_t<InputIterator>>::iterator_category, std::bidirectional_iterator_tag>::value))

#define DeflIsRandomAccessIterator (std::is_convertible<decltype(*std::decay_t<RandomAccessIterator>()), int>::value \
                                    && std::is_same<typename std::iterator_traits<std::decay_t<RandomAccessIterator>>::iterator_category, std::random_access_iterator_tag>::value)

#define DeflIsOutputIterator       (std::is_convertible<decltype(*std::decay_t<OutputIterator>()), int>::value \
                                    && (std::is_same<typename std::iterator_traits<std::decay_t<OutputIterator>>::iterator_category, std::output_iterator_tag>::value \
                                     || std::is_same<typename std::iterator_traits<std::decay_t<OutputIterator>>::iterator_category, std::forward_iterator_tag>::value \
                                     || std::is_same<typename std::iterator_traits<std::decay_t<OutputIterator>>::iterator_category, std::bidirectional_iterator_tag>::value))

#define DeflInputAbortable_InputFunctor \
                                 (1* !(std::is_same<std::decay_t<std::result_of_t<InputFunctor()>>, unsigned char>::value \
                                    || std::is_same<std::decay_t<std::result_of_t<InputFunctor()>>,   signed char>::value \
                                    || std::is_same<std::decay_t<std::result_of_t<InputFunctor()>>,          char>::value))
#define DeflOutputAbortable_OutputFunctor \
                                 (2* std::is_same<std::result_of_t<OutputFunctor(int)>, bool>::value)
#define DeflOutputAbortable_WindowFunctor \
                                 (2* std::is_convertible<std::decay_t<std::result_of_t<WindowFunctor(int,int)>>, int>::value)

/* The functor base with window functor */
template<typename InputFunctor, typename OutputFunctor, typename WindowFunctor>
std::enable_if_t<DeflIsInputFunctor && DeflIsOutputFunctor && DeflIsWindowFunctor, int>
    Deflate(InputFunctor&& input, OutputFunctor&& output, WindowFunctor&& outputcopy)
{
    gunzip_ns::DeflateState<false> state;

    // For output to be abortable, both the output functor and window functor must have return types.
    constexpr unsigned char Abortable = DeflInputAbortable_InputFunctor
                                      | (DeflOutputAbortable_OutputFunctor & DeflOutputAbortable_WindowFunctor);

    return Deflate<Abortable>(state, std::forward<InputFunctor>(input),
                                     std::forward<OutputFunctor>(output),
                                     std::forward<WindowFunctor>(outputcopy));
}

/* The functor base without window functor */
template<typename InputFunctor, typename OutputFunctor>
std::enable_if_t<DeflIsInputFunctor && DeflIsOutputFunctor, int>
    Deflate(InputFunctor&& input, OutputFunctor&& output)
{
    // Using a library-supplied output window. OutputFunctor will be wrapped.

    gunzip_ns::DeflateState<true> state;

    constexpr unsigned char Abortable = DeflInputAbortable_InputFunctor
                                      | DeflOutputAbortable_OutputFunctor;
    auto Put = [&](unsigned char l)
    {
        state.Window.Data[state.Window.Head++ & 32767u] = l;
        return output(l);
    };

    return Deflate<Abortable> (state,
        std::forward<InputFunctor>(input),
        Put,
        [&](std::uint_least16_t length, std::uint_fast32_t offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length>0; --length)
            {
                unsigned char byte = state.Window.Data[(state.Window.Head - offs) & 32767u];
                if(gunzip_ns::OutputHelper<Abortable&2>::output(Put, byte))
                    break;
            }
            return length;
        });
}



template<typename InputFunctor, typename RandomAccessIterator>
std::enable_if_t<DeflIsInputFunctor && DeflIsRandomAccessIterator, int>
    Deflate(InputFunctor&& input, RandomAccessIterator&& target)
{
    constexpr unsigned char Abortable = DeflInputAbortable_InputFunctor; // Output is not abortable

    return Deflate<Abortable> (std::forward<InputFunctor>(input),
        [&](unsigned char l) { *target++ = l; },
        [&](std::uint_least16_t length, std::uint_fast32_t offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length--; ++target) { *target = *(target-offs); }
        });
}


template<typename InputFunctor, typename OutputIterator>
std::enable_if_t<DeflIsInputFunctor && DeflIsOutputIterator, int>
    Deflate(InputFunctor&& input, OutputIterator&& target)
{
    constexpr unsigned char Abortable = DeflInputAbortable_InputFunctor; // Output is not abortable

    return Deflate<Abortable> (std::forward<InputFunctor>(input),
                               [&](unsigned char l) { *target++ = l; });
}

template<typename InputFunctor, typename RandomAccessIterator>
std::enable_if_t<DeflIsInputFunctor && DeflIsRandomAccessIterator, int>
    Deflate(InputFunctor&& input, RandomAccessIterator&& target, std::size_t target_limit)
{
    std::size_t target_size = 0;
    // Using a window functor, not a separate window.
    return Deflate(std::forward<InputFunctor>(input),
        [&](unsigned char l)
        {
            if(target_size >= target_limit) return true;
            target[target_size++] = l;
            return false;
        },
        [&](std::uint_least16_t length, std::uint_fast32_t offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length > 0; ++target_size, --length)
            {
                if(target_size >= target_limit) break;
                target[target_size] = target[target_size - offs];
            }
            return length;
        });
}

template<typename InputFunctor, typename RandomAccessIterator>
std::enable_if_t<DeflIsInputFunctor && DeflIsRandomAccessIterator, int>
    Deflate(InputFunctor&& input, RandomAccessIterator&& target_begin, RandomAccessIterator&& target_end)
{
    // Using a window functor, not a separate window.
    return Deflate(std::forward<InputFunctor>(input),
        [&](unsigned char l)
        {
            if(target_begin == target_end) return true;
            *target_begin++ = l;
            return false;
        },
        [&](std::uint_least16_t length, std::uint_fast32_t offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length > 0; --length, ++target_begin)
            {
                if(target_begin == target_end) break;
                *target_begin = *(target_begin - offs);
            }
            return length;
        });
}


template<typename InputIterator, typename... Args>
std::enable_if_t<DeflIsInputIterator, int>
    Deflate(InputIterator&& input, Args&&... args)
{
    return Deflate([&]() { return *input++; },
                   std::forward<Args>(args)...);
}

template<typename ForwardIterator, typename... Args>
std::enable_if_t<DeflIsForwardIterator, int>
    Deflate(ForwardIterator&& begin, ForwardIterator&& end,  Args&&... args)
{
    return Deflate([&]()                { return begin==end ? -1 : *begin++; },
                   std::forward<Args>(args)...);
}

template<typename ForwardIterator, typename... Args>
std::enable_if_t<DeflIsForwardIterator, int>
    Deflate(ForwardIterator&& begin, std::size_t length,  Args&&... args)
{
    return Deflate([&]() { return length ? --length, *begin++ : -1; },
                   std::forward<Args>(args)...);
}


#undef DeflIsWindowFunctor
#undef DeflIsInputFunctor
#undef DeflIsWindowFunctor
#undef DeflIsRandomAccessIterator
#undef DeflIsForwardIterator
#undef DeflIsInputIterator
#undef DeflIsOutputIterator
#undef DeflInputAbortable_InputFunctor
#undef DeflOutputAbortable_OutputFunctor
#undef DeflOutputAbortable_WindowFunctor
