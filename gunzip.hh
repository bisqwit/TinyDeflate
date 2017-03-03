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
// Memory usage: 160 bytes for lengths array (automatic, i.e. stack)
//               2160 bytes for huffman tree (automatic, i.e. stack)
//               +miscellaneous other automatic variables
template<typename InputFunctor, typename OutputFunctor, typename WindowFunctor>
int Deflate(InputFunctor&& input, OutputFunctor&& output, WindowFunctor&& outputcopy);

// Alternative: Same as above, but window-management is handled automatically.
//              This adds 32770 bytes of automatic variables for the look-behind window.
template<typename InputFunctor, typename OutputFunctor>
int Deflate(InputFunctor&& input, OutputFunctor&& output);

// Alternative: Deflate-decompress into a memory region.
// In this case, a separate window will not be allocated.
template<typename InputFunctor>
int Deflate(InputFunctor&& input, unsigned char* target);

// Alternative: Use a pair of forward iterators to denote input range, and an output iterator
template<typename ForwardIterator, typename OutputIterator>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputIterator&& output);

// Another iterator alternative.
/*template<typename InputIterator, typename OutputIterator>
void Deflate(InputIterator&& input, OutputIterator&& output);*/

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

        template<typename GetBitsFunc>
        unsigned Read(unsigned which, GetBitsFunc&& GetBits) const
        {
            huffnode node = get(which ? branch1 : branch0);
            while(node.GetBranch1()) node = get(GetBits(1) ? node.GetBranch1() : node.GetBranch0());
            return node.GetValue();
        }
    };

    template<bool WithWindow>
    struct DeflateState
    {
        RandomAccessArray<USE_BITARRAY_FOR_LENGTHS, 288+32, 4> Lengths; // Lengths are in 0..15 range. 160 bytes are allocated.

        RandomAccessArray<USE_BITARRAY_FOR_HUFFNODES, PoolSize, HuffNodeBits> pool; // Total: 638 huffnodes (2160 bytes)
        hufftree tables_fixed{pool, 0,0,0}, tables_dyn{pool, 0,0,0}, *cur_table=nullptr;

        struct { unsigned long Cache; unsigned Count; } Bits {0,0};
    };

    template<>
    struct DeflateState<true>: public DeflateState<false>
    {
        struct { unsigned char Data[32768u]; unsigned short Head=0; } Window;
    };
}//ns

template<typename InputFunctor, typename OutputFunctor, typename WindowFunctor>
int Deflate(gunzip_ns::DeflateState<false>& state, InputFunctor&& input, OutputFunctor&& output, WindowFunctor&& outputcopy)
{
    using namespace gunzip_ns;

    // Bit-by-bit input routine
    #define GetBits_F(numbits, param, o) do { \
        unsigned long l = (numbits); \
        while(state.Bits.Count < l) \
        { \
            unsigned long byte = input(); \
            state.Bits.Cache |= (byte & 0xFF) << state.Bits.Count; \
            state.Bits.Count += 8; \
        } \
        o(param, state.Bits.Cache & ((1ul << l) - 1)); \
        state.Bits.Cache >>= l; \
        state.Bits.Count -= l; \
    } while(0)

    #define assign(target, value) (target) = (value)
    #define GetBits(numbits, target) GetBits_F(numbits, target, assign)

    #define ignore(target, value) do {} while(0)
    #define DummyGetBits(numbits) GetBits_F(numbits, target, ignore)

    #define HuffRead(tree, which, target) do { \
        huffnode node = (tree).get(which ? (tree).branch1 : (tree).branch0); \
        while(node.GetBranch1()) \
        { \
            unsigned q; GetBits(1, q); \
            node = (tree).get(q ? node.GetBranch1() : node.GetBranch0()); \
        } \
        (target) = node.GetValue(); \
    } while(0)

    #define Fail_If(condition) do { \
       assert(!(condition)); \
       if(condition) return -1; \
    } while(0)

    // Read stream header
    unsigned short header; GetBits(16, header);
    // ^ Read deflate header: method[4] ; winsize[4] ; checksum[8]
    if(header == 0x8B1F) // Is it actually a gzip header?
    {
        GetBits(8, header); Fail_If(header != 8); // Format identifier should be 8
        GetBits(8, header);                       // Get flags
        DummyGetBits(48); // MTIME (3 of 4); MTIME(1 of 4), XFL and OS
        if(header&4) // Skip extra fields as indicated by FEXTRA
            { unsigned q; GetBits(16, q); while(q--) { DummyGetBits(8); } }
        if(header&8)  for(;;) { unsigned q; GetBits(8, q); if(!q) break; } // NAME: Skip filename if FNAME was present
        if(header&16) for(;;) { unsigned q; GetBits(8, q); if(!q) break; } // COMMENT: Skip comment if FCOMMENT was present
        if(header&2)  DummyGetBits(16);         // HCRC: Skip FCRC if was present
        outputcopy(0, 32768u); // GZIP always uses 32k window
    }
    else // No. Deflate header?
    {
        Fail_If((header & 0x208F) != 0x0008 || ((((header<<8)+(header>>8))&0xFFFF)%31) != 0);
        outputcopy(0, 256 << ((header >> 4) & 0xF)); // Preset dictionary (0x2000) is not supported
    }

    // Read compressed blocks
    for(header=0; !(header & 1); )
    {
        GetBits(3, header); Fail_If(header >= 6);
        switch(header >> 1)
        {
        case 0: // copy stored block data
            DummyGetBits(state.Bits.Count%8); // Go to byte boundary (discard a few bits)
            {unsigned short a, b; GetBits(16, a); GetBits(16, b);
            Fail_If((a^b) != 0xFFFF);
            // Note: It is valid for "a" to be 0 here.
            // It is sometimes used for aligning the stream to byte boundary.
            while(a--)
            {
                GetBits(8, b);
                output(b);
            }}
            continue;
        case 1: // fixed block
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
            break;
        default: // dynamic block
            unsigned nlen, ndist, ncode;
            GetBits(5, nlen);  nlen += 257; // 257..288
            GetBits(5, ndist); ndist += 1; // 1..32
            GetBits(4, ncode); ncode += 4; // 4..19
            assert(nlen+ndist <= 288+32);
            state.Lengths.template WSet<32*4>(0, 0); // 19 needed, but round to nice unit
            for(unsigned a=0; a<19 && a<ncode; ++a)
            {
                unsigned b; GetBits(3, b);
                state.Lengths.QSet(a<3 ? (a+16) : ((a%2) ? (1-a/2)&7 : (6+a/2)), b);
            }
            // ^ 19 * 3 = 57 bits are used
            state.tables_dyn.Create(0, 19, state.Lengths, 0); // length-lengths
            assert(state.tables_dyn.used <= PoolSize);
            state.Lengths = {}; // clear at least (nlen+ndist) nibbles; easiest to clear it all
            //state.Lengths.Set<(288+32)*4,true>(0,0);
            for(unsigned end,lencode,prev_lencode=0, code=0; code < nlen+ndist; )
            {
                HuffRead(state.tables_dyn, 0, lencode); // 0-18
                switch(lencode)
                {
                    case 16: GetBits(2,end); end += code+3; lencode = prev_lencode; break;     // 3..6
                    case 17: GetBits(3,end); end += code+3; lencode = 0; break;                // 3..10
                    case 18: GetBits(7,end); end += code+11; lencode = 0; break;               // 11..138
                    default: end = code+1; prev_lencode = lencode; assert(lencode < 16); // 1 times
                }
                Fail_If(end > nlen+ndist);
                while(code < end) state.Lengths.QSet(code++, lencode);
            }
            state.tables_dyn.Create(0, nlen,  state.Lengths, 0);
            state.tables_dyn.Create(1, ndist, state.Lengths, nlen);
            assert(state.tables_dyn.used <= PoolSize);
            // ^If this assertion fails, simply increase PoolSize.
            // So far the largest value seen in the wild is 630.

            //fprintf(stderr, "pool2 size%5u\n", state.tables_dyn.used);
            state.cur_table = &state.tables_dyn;
        }
        // Do actual deflating.
        for(;;)
        {
            unsigned code;
            HuffRead(*state.cur_table, 0, code);
            if(!(code & -256))
            {
                output(code); // 0..255: literal byte
            }
            else if(!(code & 0xFF)) break; // 256=end
            else // 257..285: length code for backwards reference
            {
                unsigned a = code-257, lbits = (a >= 8 && a<28) ? (a/4-1) : 0, length, offset;
                GetBits(lbits,length); length += 3 + (a > 28 ? 0 : ((a >= 8) ? ((a%4+4) << (a/4-1)) - (a==28) : a));
                HuffRead(*state.cur_table, 1, a); // Read distance code (0..31)
                unsigned dbits = a>=4 ? a/2-1 : 0, dbase = (a>=4 ? ((2+a%2) << (a/2-1)) : a);
                GetBits(dbits, offset); offset += 1 + dbase;
                outputcopy(length, offset);
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
    return 0;
}

template<typename InputFunctor, typename OutputFunctor, typename WindowFunctor>
int Deflate(InputFunctor&& input, OutputFunctor&& output, WindowFunctor&& outputcopy)
{
    gunzip_ns::DeflateState<false> state;
    return Deflate(state, std::forward<InputFunctor>(input), std::forward<OutputFunctor>(output),
                          std::forward<WindowFunctor>(outputcopy));
}

template<typename InputFunctor, typename OutputFunctor>
int Deflate(InputFunctor&& input, OutputFunctor&& output)
{
    gunzip_ns::DeflateState<true> state;
    auto Put = [&](unsigned char l)
    {
        state.Window.Data[state.Window.Head++ & 32767u] = l;
        output(l);
    };
    return Deflate(state,
        std::forward<InputFunctor>(input),
        Put,
        [&](unsigned length, unsigned offs)
        {
            // length=0 means that offs is the size of the window.
            while(length--) { Put(state.Window.Data[(state.Window.Head - offs) & 32767u]); }
        });
}

template<typename InputFunctor>
int Deflate(InputFunctor&& input, unsigned char* target)
{
    return Deflate(std::forward<InputFunctor>(input),
        [&](unsigned char l) { *target++ = l; },
        [&](unsigned length, unsigned offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length--; ++target) { *target = *(target-offs); }
        });
}

template<typename ForwardIterator, typename OutputIterator>
int Deflate(ForwardIterator&& begin, ForwardIterator&& end, OutputIterator&& output)
{
    return Deflate([&]()                { return begin==end ? 0 : *begin++; },
                   [&](unsigned char l) { *output++ = l; });
}

/*template<typename InputIterator, typename OutputIterator>
int Deflate(InputIterator&& input, OutputIterator&& output)
{
    return Deflate([&]()                { return *input++; },
                   [&](unsigned char l) { *output++ = l; });
}*/