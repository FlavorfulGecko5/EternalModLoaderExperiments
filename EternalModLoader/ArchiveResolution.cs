using EternalModLoader.Mods.Resources;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace EternalModLoader
{
    //void innerfunc(int i) { }
    //var test = Task.Run(() => innerfunc(100));
    public static class ArchiveResolution
    {
        private static List<string> archiveNames = new List<string>();
        private static Dictionary<UInt64, short[]> fileMapping = new Dictionary<UInt64, short[]>();

        public static bool InitArchiveResolution()
        {
            if (!File.Exists("archiveresolution"))
                return false;

            byte[] rawFile = File.ReadAllBytes("archiveresolution");

            // Read the file header
            int version = BitConverter.ToInt32(rawFile, 0);
            if (version != 1) return false;
            int numArchiveNames = BitConverter.ToInt32(rawFile, 4);
            int numFileMappings = BitConverter.ToInt32(rawFile, 8);
            archiveNames = new List<string>(numArchiveNames);
            fileMapping = new Dictionary<ulong, short[]>(numFileMappings);


            // Read the resource strings
            int nextByte = 12;
            for (int i = 0; i < numArchiveNames; i++)
            {
                short stringlen = BitConverter.ToInt16(rawFile, nextByte);
                nextByte += 2;
                archiveNames.Add(Encoding.ASCII.GetString(rawFile, nextByte, stringlen));
                nextByte += stringlen;
            }

            // Read the file-to-archive mapping entries
            for(int i = 0; i < numFileMappings; i++)
            {
                ulong hash = BitConverter.ToUInt64(rawFile, nextByte); nextByte += 8;

                short indexCount = BitConverter.ToInt16(rawFile, nextByte); nextByte += 2;
                short[] indices = new short[indexCount];
                for(int k = 0; k < indexCount; k++)
                {
                    indices[k] = BitConverter.ToInt16(rawFile, nextByte); nextByte += 2;
                }
                fileMapping.Add(hash, indices);
            }
            return true;
        }

        public static string[] GetArchiveNames(string resourcePath)
        {
            if(resourcePath.EndsWith(".decl"))
            {
                resourcePath = "rs_streamfile/" + resourcePath;
            }

            ulong hash = FarmHash.FarmHash64(Encoding.ASCII.GetBytes(resourcePath));
            short[] archiveIndices;
            if (!fileMapping.TryGetValue(hash, out archiveIndices))
            {
                return new string[0];
            }

            string[] names = new string[archiveIndices.Length];
            for(int i = 0; i < names.Length; i++)
            {
                names[i] = archiveNames[archiveIndices[i]];
            }

            foreach(string s in names)
            {
                Console.WriteLine(s);
            }
            return new string[3];
        }
    }

    public static class FarmHash
    {

        private const UInt64 k0 = 0xC3A5C85C97CB3127;
        private const UInt64 k1 = 0xB492B66FBE98F273;
        private const UInt64 k2 = 0x9AE16A3B2F90404F;

        private static UInt64 Fetch(byte[] p, UInt64 offset, UInt64 startIndex)
        {
            UInt64 result;
            result = BitConverter.ToUInt64(p, (int)(startIndex + offset));
            return result; // Endianness check but it should be fine since we can assume little endian
        }

        private static UInt32 Fetch32(byte[] p, UInt64 offset, UInt64 startIndex)
        {
            UInt32 result;
            result = BitConverter.ToUInt32(p, (int)(startIndex + offset));
            return result;
        }

        private static void swapperino(ref UInt64 a, ref UInt64 b)
        {
            UInt64 temp = a;
            a = b;
            b = temp;
        }


        private static UInt64 Rotate(UInt64 val, int shift)
        {
            //return sizeof(unsigned long) == sizeof(val) ?
            //    _lrotr(val, shift) :
            //    BasicRotate64(val, shift);

            return shift == 0 ? val : ((val >> shift) | (val << (64 - shift)));
        }

        private struct Pair64
        {
            public UInt64 first;
            public UInt64 second;

            public Pair64(ulong pfirst, ulong psecond)
            {
                first = pfirst;
                second = psecond;
            }
        };

        private static UInt64 ShiftMix(UInt64 val)
        {
            return val ^ (val >> 47);
        }

        private static UInt64 HashLen16(UInt64 u, UInt64 v, UInt64 mul)
        {
            // Murmur-inspired hashing.
            UInt64 a = (u ^ v) * mul;
            a ^= (a >> 47);
            UInt64 b = (v ^ a) * mul;
            b ^= (b >> 47);
            b *= mul;
            return b;
        }

        private static UInt64 HashLen0to16(byte[] s, UInt64 offset)
        {
            UInt64 len = (UInt64)s.LongLength - offset;
            if (len >= 8)
            {
                UInt64 mul = k2 + len * 2;
                UInt64 a = Fetch(s, offset, 0) + k2;
                UInt64 b = Fetch(s, offset, len - 8);
                UInt64 c = Rotate(b, 37) * mul + a;
                UInt64 d = (Rotate(a, 25) + b) * mul;
                return HashLen16(c, d, mul);
            }
            if (len >= 4)
            {
                UInt64 mul = k2 + len * 2;
                UInt64 a = Fetch32(s, offset, 0);
                return HashLen16(len + (a << 3), Fetch32(s, offset, len - 4), mul);
            }
            if (len > 0)
            {
                byte a = s[0];
                byte b = s[len >> 1];
                byte c = s[len - 1];
                UInt32 y = (UInt32)(a) + ((UInt32)(b) << 8);
                UInt32 z = (UInt32)len + ((UInt32)(c) << 2);
                return ShiftMix(y * k2 ^ z * k0) * k2;
            }
            return k2;
        }

        // This probably works well for 16-byte strings as well, but it may be overkill
        // in that case.
        private static UInt64 HashLen17to32(byte[] s, UInt64 offset)
        {
            UInt64 len = (UInt64)s.LongLength - offset;
            UInt64 mul = k2 + len * 2;
            UInt64 a = Fetch(s, offset, 0) * k1;
            UInt64 b = Fetch(s, offset, 8);
            UInt64 c = Fetch(s, offset, len - 8) * mul;
            UInt64 d = Fetch(s, offset, len - 16) * k2;
            return HashLen16(Rotate(a + b, 43) + Rotate(c, 30) + d,
                a + Rotate(b + k2, 18) + c, mul);
        }

        // Return a 16-byte hash for 48 bytes.  Quick and dirty.
        // Callers do best to use "random-looking" values for a and b.
        private static Pair64 WeakHashLen32WithSeeds(UInt64 w, UInt64 x, UInt64 y, UInt64 z, UInt64 a, UInt64 b)
        {
            a += w;
            b = Rotate(b + a + z, 21);
            UInt64 c = a;
            a += x;
            a += y;
            b += Rotate(a, 44);

            Pair64 result = new Pair64(0, 0);
            result.first = a + z;
            result.second = b + c;
            return result;
        }

        // Return a 16-byte hash for s[0] ... s[31], a, and b.  Quick and dirty.
        private static Pair64 WeakHashLen32WithSeeds(byte[] s, UInt64 offset, UInt64 a, UInt64 b)
        {
            return WeakHashLen32WithSeeds(Fetch(s, offset, 0), Fetch(s, offset, 8), Fetch(s, offset, 16), Fetch(s, offset, 24), a, b);
        }

        // Return an 8-byte hash for 33 to 64 bytes.
        private static UInt64 HashLen33to64(byte[] s, UInt64 offset)
        {
            UInt64 len = (UInt64)s.LongLength - offset;
            UInt64 mul = k2 + len * 2;
            UInt64 a = Fetch(s, offset, 0) * k2;
            UInt64 b = Fetch(s, offset, 8);
            UInt64 c = Fetch(s, offset, len - 8) * mul;
            UInt64 d = Fetch(s, offset, len - 16) * k2;
            UInt64 y = Rotate(a + b, 43) + Rotate(c, 30) + d;
            UInt64 z = HashLen16(y, a + Rotate(b + k2, 18) + c, mul);
            UInt64 e = Fetch(s, offset, 16) * mul;
            UInt64 f = Fetch(s, offset, 24);
            UInt64 g = (y + Fetch(s, offset, len - 32)) * mul;
            UInt64 h = (z + Fetch(s, offset, len - 24)) * mul;
            return HashLen16(Rotate(e + f, 43) + Rotate(g, 30) + h,
                e + Rotate(f + a, 18) + g, mul);
        }

        public static UInt64 FarmHash64(byte[] s)
        {
            UInt64 len = (UInt64)s.LongLength;
            const UInt64 seed = 81;
            if (len <= 32)
            {
                if (len <= 16)
                {
                    return HashLen0to16(s, 0);
                }
                else
                {
                    return HashLen17to32(s, 0);
                }
            }
            else if (len <= 64)
            {
                return HashLen33to64(s, 0);
            }

            // For strings over 64 bytes we loop.  Internal state consists of
            // 56 bytes: v, w, x, y, and z.
            UInt64 x = seed;
            UInt64 y; unchecked { y = seed * k1 + 113; }
            UInt64 z = ShiftMix(y * k2 + 113) * k2;
            Pair64 v = new Pair64(0, 0);
            Pair64 w = new Pair64(0, 0);
            x = x * k2 + Fetch(s, 0, 0);

            // Set end so that after the loop we have 1 to 64 bytes left to process.
            UInt64 endOff = ((len - 1) / 64) * 64;
            UInt64 last64Off = endOff + ((len - 1) & 63) - 63;
            UInt64 sOff = 0;
            //const char* end = s + ((len - 1) / 64) * 64;
            //const char* last64 = end + ((len - 1) & 63) - 63;
            //assert(s + len - 64 == last64);
            do
            {
                x = Rotate(x + y + v.first + Fetch(s, sOff, 8), 37) * k1;
                y = Rotate(y + v.second + Fetch(s, sOff, 48), 42) * k1;
                x ^= w.second;
                y += v.first + Fetch(s, sOff, 40);
                z = Rotate(z + w.first, 33) * k1;
                v = WeakHashLen32WithSeeds(s, sOff, v.second * k1, x + w.first);
                w = WeakHashLen32WithSeeds(s, sOff + 32, z + w.second, y + Fetch(s, sOff, 16));
                swapperino(ref z, ref x);
                sOff += 64;
            } while (sOff != endOff);
            UInt64 mul = k1 + ((z & 0xff) << 1);
            // Make s point to the last 64 bytes of input.
            sOff = last64Off;
            w.first += ((len - 1) & 63);
            v.first += w.first;
            w.first += v.first;
            x = Rotate(x + y + v.first + Fetch(s, sOff, 8), 37) * mul;
            y = Rotate(y + v.second + Fetch(s, sOff, 48), 42) * mul;
            x ^= w.second * 9;
            y += v.first * 9 + Fetch(s, sOff, 40);
            z = Rotate(z + w.first, 33) * mul;
            v = WeakHashLen32WithSeeds(s, sOff, v.second * mul, x + w.first);
            w = WeakHashLen32WithSeeds(s, sOff + 32, z + w.second, y + Fetch(s, sOff, 16));
            swapperino(ref z, ref x);
            return HashLen16(HashLen16(v.first, w.first, mul) + ShiftMix(y) * k0 + z, HashLen16(v.second, w.second, mul) + x, mul);
        }

    }
}
