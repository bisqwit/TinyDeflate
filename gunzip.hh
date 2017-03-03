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
#include <type_traits>
#include <utility>     // std::forward

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

// Alternative: Same as above, but window-management is handled automatically.
//              This adds 32770 bytes of automatic variables for the look-behind window.
template<typename InputFunctor, typename OutputFunctor>
int Deflate(InputFunctor&& input, OutputFunctor&& output);

// Alternative: Deflate-decompress into a memory region.
// In this case, a separate window will not be allocated.
template<typename InputFunctor, typename RandomAccessIterator>
int Deflate(InputFunctor&& input, RandomAccessIterator&& target);

// Same as above, but with a length limit. Decompression aborts if the length limit is hit.
template<typename InputFunctor, typename RandomAccessIterator>
int Deflate(InputFunctor&& input, RandomAccessIterator&& target, std::size_t target_limit);

// Same as above, but with the length expressed as an iterator pair.
template<typename InputFunctor, typename RandomAccessIterator>
int Deflate(InputFunctor&& input, RandomAccessIterator&& target_begin, RandomAccessIterator&& target_end);

// Alternative: Use a pair of forward iterators to denote input range, and an output iterator
template<typename ForwardIterator, typename OutputIterator>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputIterator&& output);

// Alternative: Use a pair of forward iterators to denote input range, and an output functor
template<typename ForwardIterator, typename OutputFunctor>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputFunctor&& output);

// Alternative: Use a pair of forward iterators to denote input range, and an output functor, and a window functor
template<typename ForwardIterator, typename OutputFunctor, typename WindowFunctor>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputFunctor&& output, WindowFunctor&& outputcopy);

// Alternative: Use an input iterator and an output iterator.
template<typename InputIterator, typename OutputIterator>
void Deflate(InputIterator&& input, OutputIterator&& output);

// Alterantive: Iterator pairs for both input and output. A window is allocated.
template<typename ForwardIterator, typename RandomAccessIterator>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, RandomAccessIterator&& target_begin, RandomAccessIterator&& target_end);

#endif


// The rest of the file is just for the curious about implementation.
namespace gunzip_ns
{
    // If you want more performance at the expense of RAM use,
    // Turn one or more of these settings to false:
    static constexpr bool USE_BITARRAY_TEMPORARY_IN_HUFFMAN_CREATION = true; /* 12 bytes save */
    static constexpr bool USE_BITARRAY_FOR_LENGTHS = true;                   /* 160 bytes save */
    static constexpr bool USE_BITARRAY_FOR_HUFFNODES = true;                 /* 392 bytes save */
}

// RandomAccessBitArray: An engine for arrays of data items that are smaller than a byte
template<typename U = unsigned long long>
struct RandomAccessBitArrayBase
{
    static constexpr unsigned Ubytes = sizeof(U), Ubits = Ubytes*8;

    template<unsigned Size>
    static unsigned long long Get(const U* data, unsigned index)
    {
        unsigned bitpos = index*Size, unitpos = bitpos / Ubits, shift = bitpos % Ubits;
        unsigned long long result = data[unitpos] >> shift;
        assert(Size <= sizeof(result)*8);
        unsigned acquired = Ubits - shift;
        for(; acquired < Size; acquired += Ubits)
        {
            result += (unsigned long long)data[++unitpos] << acquired;
        }
        return (Size >= sizeof(result)*8) ? result : (result & ((1ull << Size)-1));
    }

    template<unsigned Size, bool update = false>
    static void Set(U* data, unsigned index, unsigned long long value)
    {
        unsigned bitpos = index*Size, unitpos = bitpos / Ubits, eat = 0;
        // Make sure our storage unit is at least as bit as value
        assert(Ubits >= sizeof(value)*8);
        //assert(Size >= sizeof(value)*8 || value < (1ull << Size));

        if(Size % Ubits != 0)
        {
            unsigned shift = bitpos % Ubits;
            eat = Ubits - shift; if(eat > Size) eat = Size;

            assert(eat < sizeof(unsigned long long)*8);
            assert(shift + eat <= Ubits);
            unsigned long long vmask = (1ull << eat)-1;
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
                        unsigned long long vmask = ((1ull << eat)-1);
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

template<unsigned Nbits, typename U = unsigned long long>
struct RandomAccessBitArray
{
    static constexpr unsigned Ubytes = sizeof(U), Ubits = Ubytes*8, Nunits = (Nbits+Ubits-1)/Ubits;
    U data[Nunits];

    template<unsigned Size>
    unsigned long long Get(unsigned index) const
    {
        return RandomAccessBitArrayBase<U>::template Get<Size>(data, index);
    }

    template<unsigned Size, bool update = false>
    void Set(unsigned index, unsigned long long value)
    {
        RandomAccessBitArrayBase<U>::template Set<Size,update>(data, index, value);
    }
};

namespace gunzip_ns
{
    template<unsigned bits, int type = (bits>16) ? ((bits>32) ? 8 : 4) : ((bits>8) ? 2 : 1)>
    struct SmallestType { using result = unsigned long long; };
    template<unsigned bits> struct SmallestType<bits,1> { using result = unsigned char; };
    template<unsigned bits> struct SmallestType<bits,2> { using result = unsigned short; };
    template<unsigned bits> struct SmallestType<bits,4> { using result = unsigned; };

    template<bool packed, unsigned Dimension, unsigned ElementSize>
    struct RandomAccessArray {};

    template<unsigned Dim, unsigned Elem>
    struct RandomAccessArray<true, Dim, Elem>
    {
        RandomAccessBitArray<Dim*Elem> impl;
        inline unsigned long long Get(unsigned index) const { return impl.template Get<Elem>(index); }
        inline void Set(unsigned index, unsigned value) { impl.template Set<Elem,true>(index, value); }
        inline void QSet(unsigned index, unsigned value) { impl.template Set<Elem,false>(index, value); }
        template<unsigned Bits>
        inline void WSet(unsigned index, unsigned long long value) { impl.template Set<Bits,false>(index, value); }
    };

    template<unsigned Dim, unsigned Elem>
    struct RandomAccessArray<false, Dim, Elem>
    {
        typedef typename SmallestType<Elem>::result E;
        E data[Dim];
        inline E Get(unsigned index) const       { return data[index]; }
        inline void Set(unsigned index, E value) { data[index] = value; }
        inline void QSet(unsigned index, E value) { data[index] = value; }
        template<unsigned Bits>
        inline void WSet(unsigned index, unsigned long long value)
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
    struct huffnode
    {
        SmallestType<HuffNodeBits>::result intval; // Any integer type at least HuffNodeBits bits wide
        static_assert(sizeof(intval)*8 >= HuffNodeBits, "intval is too small");
        static constexpr unsigned BranchMul1 = USE_BITARRAY_FOR_HUFFNODES ? 640 : 1024;
        static constexpr unsigned BranchMul2 = USE_BITARRAY_FOR_HUFFNODES ? 640 : 1024;
        // BranchMul1 and BranchMul2  are arbitrary numbers both >= PoolSize
        // where log2(637 + BranchMul1*(637 + 287*BranchMul2)) < HuffNodeBits.
        // They are chosen to make fastest assembler code for the functions below.
        unsigned GetBranch0() const { return intval % BranchMul1; }
        unsigned GetBranch1() const { return (intval / BranchMul1) % BranchMul2; }
        unsigned GetValue()   const { return (intval / (BranchMul1 * BranchMul2)); }
        huffnode SetBranch0(unsigned b) { assert(b < PoolSize); return {intval += (b - GetBranch0())}; }
        huffnode SetBranch1(unsigned b) { assert(b < PoolSize); return {intval += (b - GetBranch1()) * (BranchMul1)}; }
        huffnode SetValue(unsigned b)   { assert(b < 288);      return {intval += (b - GetValue()) * (BranchMul1*BranchMul2)}; }
        static_assert(BranchMul1 >= PoolSize && BranchMul2 >= PoolSize
            && (PoolSize-1) + BranchMul1*((PoolSize-1) + 287*BranchMul2) < (1ull << HuffNodeBits), "Illegal BranchMul values");
    };
    struct hufftree
    {
        RandomAccessArray<USE_BITARRAY_FOR_HUFFNODES,PoolSize,HuffNodeBits>& storage;
        unsigned short used    : 12; // Index of the next unused node in the pool
        unsigned short branch0 : 10;
        unsigned short branch1 : 10;

        huffnode get(unsigned n) const          { return { unsigned(storage.Get(n-1)) }; }
        void     put(unsigned n, huffnode node) { storage.Set(n-1, node.intval); }

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
                unsigned len = lengths.Get(offset+a); // Note: Can be zero.
                data.Set(len+CountOffset, data.Get(len+CountOffset) + 1); // increase count
            }
            for(unsigned a = 0; a < 15; a++)
                data.Set(a+1+OffsOffset,
                         2u * (data.Get(a+OffsOffset) + data.Get(a+CountOffset)));
            // Largest values seen in wild for offs[16]: 16777216
            for(unsigned value = 0; value < num_values; ++value)
                if(unsigned length = lengths.Get(offset+value))
                {
                    huffnode node;
                    unsigned b = which ? branch1 : branch0;
                    if(b) { node = get(b); }
                    else  { if(which) {branch1 = used+1;} else {branch0 = used+1;} put(b = ++used, node = {0}); }

                    unsigned q = data.Get(length+OffsOffset); data.Set(length+OffsOffset, q+1); // q = offset[length]++
                    assert(length > 0);
                    for(q <<= (32u-length); length--; )
                    {
                        bool bit = q >> 31; q <<= 1;
                        unsigned nextb = bit ? node.GetBranch1() : node.GetBranch0();
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
        hufftree tables_fixed{pool, 0,0,0}, tables_dyn{pool, 0,0,0}, *cur_table=nullptr;
        huffnode tmpnode;

        unsigned long BitCache = 0;
        unsigned short nlen_ndist_ncode, header, code, offset;
        unsigned char BitCount = 0, state = 0, lencode, q;
    };

    template<>
    struct DeflateState<true>: public DeflateState<false>
    {
        struct { unsigned char Data[32768u]; unsigned short Head=0; } Window;
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
        static inline bool outputcopy(WindowFunctor&& outputcopy, unsigned short& length, unsigned offset)
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
        static inline bool outputcopy(WindowFunctor&& outputcopy, unsigned short& length, unsigned offset)
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
 *                no                 yes          no     1
 *               yes                  no          no     2
 *               yes                 yes          no     3
 *                                                       4 = invalid
 *                no                 yes         yes     5
 *               yes                  no         yes     6
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
    #define GetBits_F(numbits, param, o) \
        while(state.BitCount < numbits) \
        { \
            case __LINE__&0xFF: ; \
            unsigned long byte = input(); \
            if((Abortable&1) && (byte & ~0xFF)) { if(Abortable&4) { state.state=__LINE__&0xFF; } return 1; } \
            \
            state.BitCache |= (byte & 0xFF) << state.BitCount; \
            state.BitCount += 8; \
        } \
        o(param, state.BitCache & ((1ul << numbits) - 1)); \
        state.BitCache >>= numbits; \
        state.BitCount -= numbits

    #define assign(target, value) target = (value)
    #define GetBits(numbits, target) GetBits_F(numbits, target, assign)

    #define ignore(target, value) do {} while(0)
    #define DummyGetBits(numbits) GetBits_F(numbits, target, ignore)

    // Huffman tree read routine.
    #define HuffRead(tree, which, target) \
        state.tmpnode = (tree).get(which ? (tree).branch1 : (tree).branch0); \
        while(state.tmpnode.GetBranch1()) \
        { \
            GetBits(1, bool q); \
            state.tmpnode = (tree).get(q ? state.tmpnode.GetBranch1() : state.tmpnode.GetBranch0()); \
        } \
        target = state.tmpnode.GetValue()

    #define Fail_If(condition) do { \
        /*assert(!(condition));*/ \
        if(condition) return -1; \
    } while(0)

    switch((Abortable&4) ? state.state : 0u) { case 0u:;

    // Read stream header
    GetBits(16, state.header);
    // ^ Read deflate header: method[4] ; winsize[4] ; checksum[8]
    if(state.header == 0x8B1F) // Is it actually a gzip header?
    {
        GetBits(8, state.header); Fail_If(state.header != 8); // Format identifier should be 8
        GetBits(8, state.header);                       // Get flags
        DummyGetBits(48); // MTIME (3 of 4); MTIME(1 of 4), XFL and OS
        if(state.header&4) // Skip extra fields as indicated by FEXTRA
            { GetBits(16, state.code);
               while(state.code--) { DummyGetBits(8); } }
        if(state.header&8)  for(;;) { GetBits(8, bool q); if(!q) break; } // NAME: Skip filename if FNAME was present
        if(state.header&16) for(;;) { GetBits(8, bool q); if(!q) break; } // COMMENT: Skip comment if FCOMMENT was present
        if(state.header&2)  { DummyGetBits(16); }      // HCRC: Skip FCRC if was present
        outputcopy(0, 32768u); // GZIP always uses 32k window
    }
    else // No. Deflate header?
    {
        Fail_If((state.header & 0x208F) != 0x0008 || ((((state.header<<8)+(state.header>>8))&0xFFFF)%31) != 0);
        outputcopy(0, 256 << ((state.header >> 4) & 0xF)); // Preset dictionary (0x2000) is not supported
    }

    // Read compressed blocks
    for(state.header=0; !(state.header & 1); )
    {
        GetBits(3, state.header);
        if(!(state.header & 4)) // Fixed block
        {
            if(state.header < 2) // Copy stored block data
            {
                #define a state.code
                a = state.BitCount%8;
                DummyGetBits(a); // Go to byte boundary (discard a few bits)
                GetBits(16, a);
                {GetBits(16, unsigned short b);
                Fail_If((a^b) != 0xFFFF);}
                // Note: It is valid for "a" to be 0 here.
                // It is sometimes used for aligning the stream to byte boundary.
                while(a--)
                {
                    #define octet state.lencode
                    GetBits(8, octet);
                    while(OutputHelper<Abortable&2>::output(output, octet))
                    {
                        if(Abortable&4) { state.state = __LINE__&0xFF; } return 2; case __LINE__&0xFF: ;
                    }
                    #undef octet
                }
                #undef a
                continue;
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
        else // Dynamic block
        {
            Fail_If(state.header & 2);

            GetBits(14, state.nlen_ndist_ncode);
            #define nlen  (((state.nlen_ndist_ncode >> 0u) & 0x1Fu) + 257u) // 257..288
            #define ndist (((state.nlen_ndist_ncode >> 5u) & 0x1Fu) + 1u)   // 1..32
            #define ncode ( (state.nlen_ndist_ncode >>10u)          + 4u)   // 4..19
            assert(nlen+ndist <= 288+32);

            state.Lengths.template WSet<32*4>(0, 0); // 19 needed, but round to nice unit
            for(state.code=0; state.code < ncode; ++state.code)
            {
                GetBits(3, unsigned b);
                unsigned a = state.code;
                state.Lengths.QSet(a<3 ? (a+16) : ((a%2) ? (1-a/2)&7 : (6+a/2)), b);
            }
            // ^ 19 * 3 = 57 bits are used
            state.tables_dyn.Create(0, 19, state.Lengths, 0); // length-lengths
            assert(state.tables_dyn.used <= PoolSize);
            state.Lengths = {}; // clear at least (nlen+ndist) nibbles; easiest to clear it all
            //state.Lengths.Set<(288+32)*4,true>(0,0);
            for(state.code = state.lencode = 0; state.code < nlen+ndist; )
            {
                HuffRead(state.tables_dyn, 0, state.q); // 0-18
                assert(state.q < 19);

                if(!(state.q & 16))    { state.lencode = state.q * 0x11u; state.q = 1; } // 1 times (q < 16) (use q, set prev)
                else if(state.q < 17)  { GetBits(2, state.q); state.q += 3;  state.lencode = (state.lencode >> 4) * 0x11u; } // 3..6 (use prev)
                else if(state.q == 17) { GetBits(3, state.q); state.q += 3;  state.lencode &= 0xF0; }                        // 3..10   (use 0)
                else                   { GetBits(7, state.q); state.q += 11; state.lencode &= 0xF0; }                        // 11..138 (use 0)
                assert(state.q > 0);

                unsigned c = state.code, e = c + state.q, l = state.lencode & 0xF;
                Fail_If(e > (nlen+ndist));
                while(c < e) { state.Lengths.QSet(c++, l); }
                state.code = e;
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
            #undef ncode
        }
        // Do actual deflating.
        for(;;)
        {
            HuffRead(*state.cur_table, 0, state.code);
            if(!(state.code & -256)) // 0..255: literal byte
            {
                while(OutputHelper<Abortable&2>::output(output, state.code))
                {
                    if(Abortable&4) { state.state = __LINE__&0xFF; } return 2; case __LINE__&0xFF: ;
                }
            }
            else if(!(state.code & 0xFF)) break; // 256=end
            else // 257..285: length code for backwards reference
            {
                #define a      (unsigned(state.code-257))
                #define length state.nlen_ndist_ncode
                GetBits(unsigned((a >= 8 && a<28) ? (a/4-1) : 0), length);
                length += 3 + (a > 28 ? 0 : ((a >= 8) ? ((a%4+4) << (a/4-1)) - (a==28) : a));
                #undef a

                #define a state.code
                HuffRead(*state.cur_table, 1, a); // Read distance code (0..31)

                #define dbits   unsigned(a>=4 ? a/2-1 : 0)
                #define offset  state.offset
                GetBits(dbits, offset); offset += (1 + (a>=4 ? ((2+a%2) << (a/2-1)) : a));
                while(OutputHelper<Abortable&2>::outputcopy(outputcopy, length, offset))
                {
                    if(Abortable&4) { state.state = __LINE__&0xFF; } return 3; case __LINE__&0xFF: ;
                }
                #undef dbits
                #undef a
                #undef length
                #undef offset
            }
        }
    }
    // Note: after this, may come a checksum, and a trailer. Ignoring them.
    #undef GetBits_F
    #undef GetBits
    #undef DummyGetBits
    #undef assign
    #undef ignore
    #undef Fail_If
    } //switch
    return 0;
}

#define DeflIsInputFunctor         (std::is_convertible<typename std::result_of<InputFunctor()>::type,int>::value)
#define DeflIsOutputFunctor        (std::is_same<typename std::result_of<OutputFunctor(int)>::type,void>::value|1)
#define DeflIsWindowFunctor        (std::is_same<typename std::result_of<WindowFunctor(int,int)>::type,void>::value|1)
#define DeflIsRandomAccessIterator (std::is_convertible<decltype(*typename std::decay<RandomAccessIterator>::type()), int>::value)
#define DeflIsForwardIterator      (std::is_convertible<decltype(*typename std::decay<ForwardIterator>::type()), int>::value)
#define DeflIsInputIterator        (std::is_convertible<decltype(*typename std::decay<InputIterator>::type()), int>::value)

template<typename InputFunctor, typename OutputFunctor, typename WindowFunctor>
typename std::enable_if<DeflIsInputFunctor && DeflIsOutputFunctor && DeflIsWindowFunctor, int>::type
    Deflate(InputFunctor&& input, OutputFunctor&& output, WindowFunctor&& outputcopy)
{
    gunzip_ns::DeflateState<false> state;

    constexpr bool OutputAbortable = std::is_convertible<typename std::result_of<OutputFunctor(int)>::type, bool>::value
                                  && std::is_convertible<typename std::result_of<WindowFunctor(int,int)>::type, int>::value;
    constexpr bool InputAbortable  = !(std::is_same<typename std::result_of<InputFunctor()>, unsigned char>::value
                                    || std::is_same<typename std::result_of<InputFunctor()>,   signed char>::value
                                    || std::is_same<typename std::result_of<InputFunctor()>,          char>::value);
    constexpr unsigned char Abortable = (InputAbortable*1 + OutputAbortable*2);

    return Deflate<Abortable>(state, std::forward<InputFunctor>(input),
                                     std::forward<OutputFunctor>(output),
                                     std::forward<WindowFunctor>(outputcopy));
}

template<typename InputFunctor, typename OutputFunctor>
typename std::enable_if<DeflIsInputFunctor && DeflIsOutputFunctor, int>::type
    Deflate(InputFunctor&& input, OutputFunctor&& output)
{
    gunzip_ns::DeflateState<true> state;

    constexpr bool OutputAbortable = std::is_convertible<typename std::result_of<OutputFunctor(int)>::type, bool>::value;
    constexpr bool InputAbortable  = !(std::is_same<typename std::result_of<InputFunctor()>, unsigned char>::value
                                    || std::is_same<typename std::result_of<InputFunctor()>,   signed char>::value
                                    || std::is_same<typename std::result_of<InputFunctor()>,          char>::value);
    constexpr unsigned char Abortable = (InputAbortable*1 + OutputAbortable*2);

    auto Put = [&](unsigned char l)
    {
        state.Window.Data[state.Window.Head++ & 32767u] = l;
        return output(l);
    };

    return Deflate<Abortable> (state,
        std::forward<InputFunctor>(input),
        Put,
        [&](unsigned short length, unsigned offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length>0; --length)
            {
                unsigned char byte = state.Window.Data[(state.Window.Head - offs) & 32767u];
                if(gunzip_ns::OutputHelper<Abortable&2>::output(Put, byte))
                    return length;
            }
            return (unsigned short)0;
        });
}

template<typename InputFunctor, typename RandomAccessIterator>
typename std::enable_if<DeflIsInputFunctor && DeflIsRandomAccessIterator, int>::type
    Deflate(InputFunctor&& input, RandomAccessIterator&& target)
{
    constexpr bool OutputAbortable = false;
    constexpr bool InputAbortable  = !(std::is_same<typename std::result_of<InputFunctor()>, unsigned char>::value
                                    || std::is_same<typename std::result_of<InputFunctor()>,   signed char>::value
                                    || std::is_same<typename std::result_of<InputFunctor()>,          char>::value);
    constexpr unsigned char Abortable = (InputAbortable*1 + OutputAbortable*2);

    return Deflate<Abortable> (std::forward<InputFunctor>(input),
        [&](unsigned char l) { *target++ = l; },
        [&](unsigned short length, unsigned offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length--; ++target) { *target = *(target-offs); }
        });
}

template<typename InputFunctor, typename RandomAccessIterator>
typename std::enable_if<DeflIsInputFunctor && DeflIsRandomAccessIterator, int>::type
    Deflate(InputFunctor&& input, RandomAccessIterator&& target, std::size_t target_limit)
{
    std::size_t target_size = 0;
    return Deflate(std::forward<InputFunctor>(input),
        [&](unsigned char l)
        {
            if(target_size >= target_limit) return true;
            target[target_size++] = l;
            return false;
        },
        [&](unsigned short length, unsigned offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length > 0; ++target_size, --length)
            {
                if(target_size >= target_limit) break;
                target[target_size] = target[target_size - offs];
            }
            return (unsigned short)0;
        });
}

template<typename InputFunctor, typename RandomAccessIterator>
typename std::enable_if<DeflIsInputFunctor && DeflIsRandomAccessIterator, int>::type
    Deflate(InputFunctor&& input, RandomAccessIterator&& output_begin, RandomAccessIterator&& output_end)
{
    return Deflate(std::forward<InputFunctor>(input),
        [&](unsigned char l)
        {
            if(output_begin == output_end) return true;
            *output_begin++ = l;
            return false;
        },
        [&](unsigned short length, unsigned offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length > 0; --length, ++output_begin)
            {
                if(output_begin == output_end) break;
                *output_begin = *(output_begin - offs);
            }
            return (unsigned short)0;
        });
}

template<typename ForwardIterator, typename OutputIterator>
typename std::enable_if<DeflIsForwardIterator, int>::type
    Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputIterator&& output)
{
    return Deflate([&]()                { return begin==end ? -1 : *begin++; },
                   [&](unsigned char l) { *output++ = l; });
}

template<typename ForwardIterator, typename OutputFunctor>
typename std::enable_if<DeflIsForwardIterator && DeflIsOutputFunctor, int>::type
    Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputFunctor&& output)
{
    return Deflate([&]()                { return begin==end ? -1 : *begin++; },
                   std::forward<OutputFunctor>(output));
}

template<typename ForwardIterator, typename OutputFunctor, typename WindowFunctor>
typename std::enable_if<DeflIsForwardIterator && DeflIsOutputFunctor && DeflIsWindowFunctor, int>::type
    Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputFunctor&& output, WindowFunctor&& outputcopy)
{
    return Deflate([&]()                { return begin==end ? -1 : *begin++; },
                   std::forward<OutputFunctor>(output),
                   std::forward<WindowFunctor>(outputcopy));
}

template<typename InputIterator, typename OutputIterator>
typename std::enable_if<DeflIsInputIterator, int>::type
    Deflate(InputIterator&& input, OutputIterator&& output)
{
    return Deflate([&]()                { return *input++; },
                   [&](unsigned char l) { *output++ = l; });
}

template<typename ForwardIterator, typename RandomAccessIterator>
typename std::enable_if<DeflIsForwardIterator && DeflIsRandomAccessIterator, int>::type
    Deflate(ForwardIterator&& begin,             ForwardIterator&& end,
            RandomAccessIterator&& output_begin, RandomAccessIterator&& output_end)
{
    return Deflate(
        [&]() { return begin==end ? -1 : *begin++; },
        [&](unsigned char l)
        {
            if(output_begin == output_end) return true;
            *output_begin++ = l;
            return false;
        });
}

#undef DeflIsWindowFunctor
#undef DeflIsInputFunctor
#undef DeflIsWindowFunctor
#undef DeflIsRandomAccessIterator
#undef DeflIsForwardIterator
#undef DeflIsInputIterator
