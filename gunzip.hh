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
// Use a custom region-copy functor. A window will not be allocated.
// User-supplied functors:
//   input() returns the next byte from the input.
//   output(byte) outputs 1 byte.
//   outputcopy(length, offset) copies length bytes from head-offset.
//
// Memory usage: 160 bytes for lengths array
//               2168 bytes for huffman tree
//               +miscellaneous automatic variables
template<typename InputFunctor, typename OutputFunctor, typename WindowFunctor>
void Deflate(InputFunctor&& input, OutputFunctor&& output, WindowFunctor&& outputcopy);

// Alternative: Same as above, but window-management is handled automatically.
//              This adds 32770 bytes of automatic variables for the look-behind window.
template<typename InputFunctor, typename OutputFunctor>
void Deflate(InputFunctor&& input, OutputFunctor&& output);

// Alternative: Deflate to a memory region.
// In this case, a separate window will not be allocated.
template<typename InputFunctor>
void Deflate(InputFunctor&& input, unsigned char* target);

// The rest of the file is just for the curious about implementation.

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

template<unsigned Nbits, typename U = unsigned long>
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
    static constexpr unsigned HuffNodeBits = 27, PoolSize = 642; // 638 for fixed tables
    struct huffnode
    {
        static constexpr unsigned BranchMul = 672; //Any number between PoolSize..682 
        unsigned intval;
        // Branches are in 0..641 range (number of pool indexes). --> 9.33 bits needed
        // Values are in 0..287 range.                            --> 8.17 bits needed
        // Minimum theoretically possible is 26.823 bits.
        unsigned GetBranch0() const { return intval % BranchMul; }
        unsigned GetBranch1() const { return (intval / BranchMul) % BranchMul; }
        unsigned GetValue()   const { return (intval / (BranchMul * BranchMul)); }
        huffnode SetBranch0(unsigned b) { assert(b < BranchMul); return {intval += (b - GetBranch0())}; }
        huffnode SetBranch1(unsigned b) { assert(b < BranchMul); return {intval += (b - GetBranch1()) * (BranchMul)}; }
        huffnode SetValue(unsigned b)   { assert(b < 288);       return {intval += (b - GetValue()) * (BranchMul*BranchMul)}; }
    };
    struct hufftree
    {
        RandomAccessBitArray<PoolSize*HuffNodeBits>& storage;
        unsigned short used    : 12; // Index of the next unused node in the pool
        unsigned short branch0 : 10;
        unsigned short branch1 : 10;

        huffnode get(unsigned n) const          { return { unsigned(storage.Get<HuffNodeBits>(n-1)) }; }
        void     put(unsigned n, huffnode node) { storage.Set<HuffNodeBits,true>(n-1, node.intval); }

        // Create a huffman tree for num_values, with given lengths.
        // The tree will be put in branch[which]; other branch not touched.
        // Length = how many bits to use for encoding this value.
        void Create(unsigned which, unsigned num_values, const RandomAccessBitArray<(288+32)*4>& lengths, unsigned offset)
        {
            if(!which) { used=0; branch0=0; branch1=0; }
            unsigned data[17] {0}, *offs=data+0, *count=data+1;
            for(unsigned a = 0; a < num_values; ++a) count[lengths.Get<4>(offset+a)] += 1; // How many times each length appears
            for(unsigned a = 0; a < 15; a++) offs[a + 1] = (offs[a] + count[a]) * 2u;
            // Largest values seen in wild for offs[16]: 16777216
            for(unsigned value = 0; value < num_values; ++value)
                if(unsigned length = lengths.Get<4>(offset+value))
                {
                    huffnode node;
                    unsigned b = which ? branch1 : branch0;
                    if(b) { node = get(b); }
                    else  { if(which) {branch1 = used+1;} else {branch0 = used+1;} put(b = ++used, node = {0}); }

                    for(unsigned q = offs[length]++ << (32u-length); length--; )
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
}

template<typename InputFunctor, typename OutputFunctor, typename WindowFunctor>
void Deflate(InputFunctor&& input, OutputFunctor&& output, WindowFunctor&& outputcopy)
{
    using namespace gunzip_ns;
    // Bit-by-bit input routine
    struct { unsigned long Cache; unsigned Count; } Bits {0,0};
    auto GetBits = [&Bits,&input](unsigned l)
    {
        for (; Bits.Count < l; Bits.Count += 8)
            Bits.Cache |= (input() & 0xFFul) << Bits.Count;
        unsigned w = Bits.Cache & ((1ul << l) - 1);
        Bits.Cache >>= l;
        Bits.Count -= l;
        //fprintf(stderr, "GetBits(%u)->%u\n", l, w);
        return w;
    };

    // Read stream header
    unsigned short header = GetBits(16), winsize = 32768u;
    // ^ Read deflate header: method[4] ; winsize[4] ; checksum[8]
    if(header == 0x8B1F) // Is it actually a gzip header?
    {
        unsigned fmt = GetBits(8), o = GetBits(8); // Get format & flags
        assert(fmt == 8);
        GetBits(48); // MTIME (3 of 4); MTIME(1 of 4), XFL and OS
        if(o&4) // Skip extra fields as indicated by FEXTRA
            for(unsigned q = GetBits(16); q--; GetBits(8));
        if(o&8)  while(GetBits(8)) {} // NAME: Skip filename if FNAME was present
        if(o&16) while(GetBits(8)) {} // COMMENT: Skip comment if FCOMMENT was present
        if(o&2)  GetBits(16);         // HCRC: Skip FCRC if was present
    }
    else // No. Deflate header?
    {
        assert((header & 0x208F) == 0x0008 && !((((header<<8)+(header>>8))&0xFFFF)%31));
        winsize = 256 << ((header >> 4) & 0xF); // Preset dictionary (0x2000) is not supported
    }
    outputcopy(0, winsize);

    // Function for reading a huffman-encoded value from bitstream.
    RandomAccessBitArray<PoolSize*HuffNodeBits> pool; // Total: 642 huffnodes (2168 bytes)
    hufftree tables_fixed{pool, 0,0,0}, tables_dyn{pool, 0,0,0}, *cur_table=nullptr;

    // Read compressed blocks
    RandomAccessBitArray<(288+32)*4> Lengths; // Lengths are in 0..15 range. 160 bytes are allocated.
    for(bool last=false; !last; )
    {
        switch(last=GetBits(1), header=GetBits(2))
        {
        case 0: // copy stored block data
            GetBits(Bits.Count%8); // Go to byte boundary (discard a few bits)
            {unsigned a = GetBits(16), b = GetBits(16);
            assert(a == (b^0xFFFF));
            // Note: It is valid for "a" to be 0 here.
            // It is sometimes used for aligning the stream to byte boundary.
            while(a--) output(GetBits(8)); }
            continue;
        case 1: // fixed block
            if(cur_table != &tables_fixed)
            {
                for(unsigned n=0; n<9; ++n) Lengths.Set<64,true>((n*16+0)/16,    0x8888888888888888ull);
                for(unsigned n=0; n<7; ++n) Lengths.Set<64,true>((n*16+0x90)/16, 0x9999999999999999ull);
                for(unsigned n=0; n<4; ++n) Lengths.Set<32,true>((n*8+0x100)/8,  (7+n/3)*0x11111111u);
                for(unsigned n=0; n<2; ++n) Lengths.Set<64,true>((n*16+0x120)/16,0x5555555555555555ull);
                tables_fixed.Create(0, 288, Lengths, 0);   // 575 used here
                tables_fixed.Create(1, 32,  Lengths, 288); // 63 used here
                assert(tables_fixed.used == 638 && tables_fixed.used <= PoolSize);
                // ^pool1 has always 638 elements. If this assertion fails,
                // something is wrong. Maybe coincidentally same as (288+32-1)*2.
                cur_table = &tables_fixed;
            }
            break;
        default: // dynamic block
            assert(header==2);
            unsigned nlen = GetBits(5) + 257; // 257..288
            unsigned ndist = GetBits(5) + 1; // 1..32
            unsigned ncode = GetBits(4) + 4; // 4..19
            assert(nlen+ndist <= 288+32);
            Lengths.Set<32*4,true>(0,0); // 19 needed, but round to nice unit
            for(unsigned a=0; a<19 && a<ncode; ++a) Lengths.Set<4>(a<3 ? (a+16) : ((a%2) ? (1-a/2)&7 : (6+a/2)), GetBits(3));
            // ^ 19 * 3 = 57 bits are used
            tables_dyn.Create(0, 19, Lengths, 0); // length-lengths
            assert(tables_dyn.used <= PoolSize);
            Lengths = {}; // clear at least (nlen+ndist) nibbles; easiest to clear it all
            //Lengths.Set<(288+32)*4,true>(0,0);
            for(unsigned end,lencode,prev_lencode=0, code=0; code < nlen+ndist; )
            {
                switch(lencode = tables_dyn.Read(0, GetBits)) // 0-18
                {
                    case 16: end = code+3+GetBits(2); lencode = prev_lencode; break;     // 3..6
                    case 17: end = code+3+GetBits(3); lencode = 0; break;                // 3..10
                    case 18: end = code+11+GetBits(7); lencode = 0; break;               // 11..138
                    default: end = code+1; prev_lencode = lencode; assert(lencode < 16); // 1 times
                }
                assert(end <= nlen+ndist);
                while(code < end) Lengths.Set<4>(code++, lencode);
            }
            tables_dyn.Create(0, nlen,  Lengths, 0);
            tables_dyn.Create(1, ndist, Lengths, nlen);
            assert(tables_dyn.used <= PoolSize);
            // ^If this assertion fails, simply increase Pool2size.
            //  Try e.g. 2048-Pool1size.
            // So far the largest value seen in the wild is 630.

            //fprintf(stderr, "pool2 size%5u\n", tables_dyn.used);
            cur_table = &tables_dyn;
        }
        // Do actual deflating.
        for(;;)
        {
            unsigned code = cur_table->Read(0, GetBits);
            if(!(code & -256)) output(code); // 0..255: literal byte
            else if(!(code & 0xFF)) break; // 256=end
            else // 257..285: length code for backwards reference
            {
                unsigned a = code-257, lbits = (a >= 8 && a<28) ? (a/4-1) : 0;
                unsigned length = 3 + GetBits(lbits) + (a > 28 ? 0 : ((a >= 8) ? ((a%4+4) << (a/4-1)) - (a==28) : a));
                a = cur_table->Read(1, GetBits); // Read distance code (0..31)
                unsigned dbits = a>=4 ? a/2-1 : 0, dbase = (a>=4 ? ((2+a%2) << (a/2-1)) : a);
                outputcopy(length, 1 + dbase + GetBits(dbits));
            }
        }
    }
    // Note: after this, may come a checksum, and a trailer. Ignoring them.
}

template<typename InputFunctor, typename OutputFunctor>
void Deflate(InputFunctor&& input, OutputFunctor&& output)
{
    struct { unsigned char Data[32768u]; unsigned short Head; } Window;
    auto Put = [&](unsigned char l)
    {
        Window.Data[Window.Head++ & 32767u] = l;
        output(l);
    };
    Deflate(std::forward<InputFunctor>(input),
        Put,
        [&](unsigned length, unsigned offs)
        {
            // length=0 means that offs is the size of the window.
            while(length--) { Put(Window.Data[(Window.Head - offs) & 32767u]); }
        });
}

template<typename InputFunctor>
void Deflate(InputFunctor&& input, unsigned char* target)
{
    Deflate(std::forward<InputFunctor>(input),
        [&](unsigned char l) { *target++ = l; },
        [&](unsigned length, unsigned offs)
        {
            // length=0 means that offs is the size of the window.
            for(; length--; ++target) { *target = *(target-offs); }
        });
}
