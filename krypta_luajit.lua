#!/usr/bin/env luajit
-- Krypta by fuka@fuxoft.cz
-- https://github.com/fuxoft/krypta
-- If you don't know exactly what all of this does, please don't use it, you could lose money.
_G.VERSION = string.match([[*<= Version '20180406b' =>*]], "'(.*)'")

--[[
	Set the SALT to something you can easily remember.
	For example your e-mail, your phone number or your full date of birth.
	It can be fairly obvious info, known to people around you
	but it should be fairly unique
	so it SHOULD NOT be the name of your pet or your favorite food or color.
]]
local SALT = "" --Put the SALT between the quotes.
local DIFFICULTY = 0 --Put desired difficulty here
local CHECKSUM = nil --Put three digit hex checksum here - for example 0x123

local bxor, band, bor, ror, rol, tohex, tobit, bnot, rshift, lshift = bit.bxor, bit.band, bit.bor, bit.ror, bit.rol, bit.tohex, bit.tobit, bit.bnot, bit.rshift, bit.lshift

local MAXDIFC = 31

local function hex256(dwords, separator)
	assert(#dwords == 8)
	separator = separator or ""
	assert(type(separator)=="string")
	local res = {}
	for i = 1, 8 do
		res[i] = tohex(dwords[i])
	end
	return table.concat(res,separator)
end

--RSA256 implementation from https://github.com/JustAPerson/LuaCrypt/
--- Round constants
-- computed as the fractional parts of the cuberoots of the first 64 primes
local k256 = {
	0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
	0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
	0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
	0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
	0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
	0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
	0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
	0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
	0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
	0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
	0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
	0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
	0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
	0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
	0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
	0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
 }
 
--- Preprocess input message
local function preprocess256(input)
	local length = #input;	-- length in bits
	local padding = (-length-9) % 64
	input = input .. "\128" .. ("\0"):rep(padding) .. "\0\0\0\0";
	local l = length * 8
	for i = 1, 4 do
		l = rol(l, 8)
		input = input .. string.char(band(l,0xff))
	end
	return input
end

--- Process an individual block using SHA256
-- Note: Lua arrays start at 1, not 0.
--       This behavior is respected in loop counters.
--
--@param `input` is the original input message
--@param `t` is the position of the first byte of this block
--@param `H` is the internal hash state
local function digest_block256(input, t, H)
	local s10	-- Using 1 var for s0,s1 to help LuaJIT register alloc
	local t1, t2
	local chmaj	-- May be used in place of s0
	local word
	local a, b, c, d, e, f, g, h
	local k = k256

	local W = {}
	local chunk
	local c1 = 0	-- #W, #words
	chunk = input:sub(t, t + 63)
	c1 = 0
	for i = 1, 64, 4 do
		c1 = c1 + 1;
		local num = 0
		for j = 0, 3 do
			num = rol(num, 8)
			num = bor(num, string.byte(chunk:sub(i+j, i+j)))
		end
		W[c1] = num
	end

	-- Extend 16 words into 64
	for t = 17, 64 do
		word  = W[t - 2]
		s10   = bxor(ror(word, 17), ror(word, 19), rshift(word, 10))
		word  = W[t - 15]
		chmaj = bxor(ror(word, 7), ror(word, 18), rshift(word, 3))
		W[t]  = s10 + W[t - 7] + chmaj + W[t - 16]
	end

	a, b, c, d = H[1], H[2], H[3], H[4];
	e, f, g, h = H[5], H[6], H[7], H[8];

	for t = 1, 64 do
		s10   = bxor(ror(e, 6), ror(e, 11), ror(e, 25));
		chmaj = bxor(band(e, f), band(bnot(e), g));
		t1    = h + s10 + chmaj + k[t] + W[t];
		s10   = bxor(ror(a, 2), ror(a, 13), ror(a, 22));
		chmaj = bxor(band(a, b), band(a, c), band(b, c));
		t2    = s10 + chmaj;
		h = g;
		g = f;
		f = e;
		e = d  + t1;
		d = c;
		c = b;
		b = a;
		a = t1 + t2;
	end

	H[1] = (a + H[1])
	H[2] = (b + H[2])
	H[3] = (c + H[3])
	H[4] = (d + H[4])
	H[5] = (e + H[5])
	H[6] = (f + H[6])
	H[7] = (g + H[7])
	H[8] = (h + H[8])
	for i = 1, 8 do
		H[i] = band(H[i],0xffffffff)
	end

end

--- Calculate the SHA256 digest of a message
-- Note: sha256() does not use variable names complaint with FIPS 180-2
--@param `input` the message
local function sha256(input, format)
	input  = preprocess256(input);
	local state  = {
		0x6a09e667,
		0xbb67ae85,
		0x3c6ef372,
		0xa54ff53a,
		0x510e527f,
		0x9b05688c,
		0x1f83d9ab,
		0x5be0cd19,
	}

	for i = 1, #input, 64 do
		digest_block256(input, i, state);
	end

	if format == "dwords" then
		return state
	end

	return hex256(state)
end
 ----- END SHA256
 

local function load_qr()
	local _M = {}
	--- The qrcode library is licensed under the 3-clause BSD license (aka "new BSD")
	--- To get in contact with the author, mail to <gundlach@speedata.de>.
	---
	--- Please report bugs on the [github project page](http://speedata.github.com/luaqrcode/).
	-- Copyright (c) 2012, Patrick Gundlach
	-- All rights reserved.
	--
	-- Redistribution and use in source and binary forms, with or without
	-- modification, are permitted provided that the following conditions are met:
	--	 * Redistributions of source code must retain the above copyright
	--	   notice, this list of conditions and the following disclaimer.
	--	 * Redistributions in binary form must reproduce the above copyright
	--	   notice, this list of conditions and the following disclaimer in the
	--	   documentation and/or other materials provided with the distribution.
	--	 * Neither the name of the <organization> nor the
	--	   names of its contributors may be used to endorse or promote products
	--	   derived from this software without specific prior written permission.
	--
	-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
	-- ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
	-- WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
	-- DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
	-- DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
	-- (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
	-- LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
	-- ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
	-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
	-- SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


	--- Overall workflow
	--- ================
	--- The steps to generate the qrcode, assuming we already have the codeword:
	---
	--- 1. Determine version, ec level and mode (=encoding) for codeword
	--- 1. Encode data
	--- 1. Arrange data and calculate error correction code
	--- 1. Generate 8 matrices with different masks and calculate the penalty
	--- 1. Return qrcode with least penalty
	---
	--- Each step is of course more or less complex and needs further description

	--- Helper functions
	--- ================
	---
	--- We start with some helper functions

	-- Return a number that is the result of interpreting the table tbl (msb first)
	local function tbl_to_number(tbl)
		local n = #tbl
		local rslt = 0
		local power = 1
		for i = 1, n do
			rslt = rslt + tbl[i]*power
			power = power*2
		end
		return rslt
	end

	-- Calculate bitwise xor of bytes m and n. 0 <= m,n <= 256.
	local function bit_xor(m, n)
		return bit.band(0xff, bit.bxor(m, n))
	end

	-- Return the binary representation of the number x with the width of `digits`.
	local function binary(x,digits)
	local s=string.format("%o",x)
	local a={["0"]="000",["1"]="001", ["2"]="010",["3"]="011",
			["4"]="100",["5"]="101", ["6"]="110",["7"]="111"}
	s=string.gsub(s,"(.)",function (d) return a[d] end)
	-- remove leading 0s
	s = string.gsub(s,"^0*(.*)$","%1")
	local fmtstring = string.format("%%%ds",digits)
	local ret = string.format(fmtstring,s)
	return string.gsub(ret," ","0")
	end

	-- A small helper function for add_typeinfo_to_matrix() and add_version_information()
	-- Add a 2 (black by default) / -2 (blank by default) to the matrix at position x,y
	-- depending on the bitstring (size 1!) where "0"=blank and "1"=black.
	local function fill_matrix_position(matrix,bitstring,x,y)
		if bitstring == "1" then
			matrix[x][y] = 2
		else
			matrix[x][y] = -2
		end
	end


	--- Step 1: Determine version, ec level and mode for codeword
	--- ========================================================
	---
	--- First we need to find out the version (= size) of the QR code. This depends on
	--- the input data (the mode to be used), the requested error correction level
	--- (normally we use the maximum level that fits into the minimal size).

	-- Return the mode for the given string `str`.
	-- See table 2 of the spec. We only support mode 1, 2 and 4.
	-- That is: numeric, alaphnumeric and binary.
	local function get_mode( str )
		local mode
		if string.match(str,"^[0-9]+$") then
			return 1
		elseif string.match(str,"^[0-9A-Z $%%*./:+-]+$") then
			return 2
		else
			return 4
		end
		assert(false,"never reached")
		return nil
	end



	--- Capacity of QR codes
	--- --------------------
	--- The capacity is calculated as follow: \\(\text{Number of data bits} = \text{number of codewords} * 8\\).
	--- The number of data bits is now reduced by 4 (the mode indicator) and the length string,
	--- that varies between 8 and 16, depending on the version and the mode (see method `get_length()`). The
	--- remaining capacity is multiplied by the amount of data per bit string (numeric: 3, alphanumeric: 2, other: 1)
	--- and divided by the length of the bit string (numeric: 10, alphanumeric: 11, binary: 8, kanji: 13).
	--- Then the floor function is applied to the result:
	--- $$\Big\lfloor \frac{( \text{#data bits} - 4 - \text{length string}) * \text{data per bit string}}{\text{length of the bit string}} \Big\rfloor$$
	---
	--- There is one problem remaining. The length string depends on the version,
	--- and the version depends on the length string. But we take this into account when calculating the
	--- the capacity, so this is not really a problem here.

	-- The capacity (number of codewords) of each version (1-40) for error correction levels 1-4 (LMQH).
	-- The higher the ec level, the lower the capacity of the version. Taken from spec, tables 7-11.
	local capacity = {
	{  19,   16,   13,	9},{  34,   28,   22,   16},{  55,   44,   34,   26},{  80,   64,   48,   36},
	{ 108,   86,   62,   46},{ 136,  108,   76,   60},{ 156,  124,   88,   66},{ 194,  154,  110,   86},
	{ 232,  182,  132,  100},{ 274,  216,  154,  122},{ 324,  254,  180,  140},{ 370,  290,  206,  158},
	{ 428,  334,  244,  180},{ 461,  365,  261,  197},{ 523,  415,  295,  223},{ 589,  453,  325,  253},
	{ 647,  507,  367,  283},{ 721,  563,  397,  313},{ 795,  627,  445,  341},{ 861,  669,  485,  385},
	{ 932,  714,  512,  406},{1006,  782,  568,  442},{1094,  860,  614,  464},{1174,  914,  664,  514},
	{1276, 1000,  718,  538},{1370, 1062,  754,  596},{1468, 1128,  808,  628},{1531, 1193,  871,  661},
	{1631, 1267,  911,  701},{1735, 1373,  985,  745},{1843, 1455, 1033,  793},{1955, 1541, 1115,  845},
	{2071, 1631, 1171,  901},{2191, 1725, 1231,  961},{2306, 1812, 1286,  986},{2434, 1914, 1354, 1054},
	{2566, 1992, 1426, 1096},{2702, 2102, 1502, 1142},{2812, 2216, 1582, 1222},{2956, 2334, 1666, 1276}}


	--- Return the smallest version for this codeword. If `requested_ec_level` is supplied,
	--- then the ec level (LMQH - 1,2,3,4) must be at least the requested level.
	-- mode = 1,2,4,8
	local function get_version_eclevel(len,mode,requested_ec_level)
		local local_mode = mode
		if mode == 4 then
			local_mode = 3
		elseif mode == 8 then
			local_mode = 4
		end
		assert( local_mode <= 4 )

		local bytes, bits, digits, modebits, c
		local tab = { {10,9,8,8},{12,11,16,10},{14,13,16,12} }
		local minversion = 40
		local maxec_level = requested_ec_level or 1
		local min,max = 1, 4
		if requested_ec_level and requested_ec_level >= 1 and requested_ec_level <= 4 then
			min = requested_ec_level
			max = requested_ec_level
		end
		for ec_level=min,max do
			for version=1,#capacity do
				bits = capacity[version][ec_level] * 8
				bits = bits - 4 -- the mode indicator
				if version < 10 then
					digits = tab[1][local_mode]
				elseif version < 27 then
					digits = tab[2][local_mode]
				elseif version <= 40 then
					digits = tab[3][local_mode]
				end
				modebits = bits - digits
				if local_mode == 1 then -- numeric
					c = math.floor(modebits * 3 / 10)
				elseif local_mode == 2 then -- alphanumeric
					c = math.floor(modebits * 2 / 11)
				elseif local_mode == 3 then -- binary
					c = math.floor(modebits * 1 / 8)
				else
					c = math.floor(modebits * 1 / 13)
				end
				if c >= len then
					if version <= minversion then
						minversion = version
						maxec_level = ec_level
					end
					break
				end
			end
		end
		return minversion, maxec_level
	end

	-- Return a bit string of 0s and 1s that includes the length of the code string.
	-- The modes are numeric = 1, alphanumeric = 2, binary = 4, and japanese = 8
	local function get_length(str,version,mode)
		local i = mode
		if mode == 4 then
			i = 3
		elseif mode == 8 then
			i = 4
		end
		assert( i <= 4 )
		local tab = { {10,9,8,8},{12,11,16,10},{14,13,16,12} }
		local digits
		if version < 10 then
			digits = tab[1][i]
		elseif version < 27 then
			digits = tab[2][i]
		elseif version <= 40 then
			digits = tab[3][i]
		else
			assert(false, "get_length, version > 40 not supported")
		end
		local len = binary(#str,digits)
		return len
	end

	--- If the `requested_ec_level` or the `mode` are provided, this will be used if possible.
	--- The mode depends on the characters used in the string `str`. It seems to be
	--- possible to split the QR code to handle multiple modes, but we don't do that.
	local function get_version_eclevel_mode_bistringlength(str,requested_ec_level,mode)
		local local_mode
		if mode then
			assert(false,"not implemented")
			-- check if the mode is OK for the string
			local_mode = mode
		else
			local_mode = get_mode(str)
		end
		local version, ec_level
		version, ec_level = get_version_eclevel(#str,local_mode,requested_ec_level)
		local length_string = get_length(str,version,local_mode)
		return version,ec_level,binary(local_mode,4),local_mode,length_string
	end

	--- Step 2: Encode data
	--- ===================

	--- There are several ways to encode the data. We currently support only numeric, alphanumeric and binary.
	--- We already chose the encoding (a.k.a. mode) in the first step, so we need to apply the mode to the
	--- codeword.
	---
	--- **Numeric**: take three digits and encode them in 10 bits
	--- **Alphanumeric**: take two characters and encode them in 11 bits
	--- **Binary**: take one octet and encode it in 8 bits

	local asciitbl = {
			-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,  -- 0x01-0x0f
		-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,  -- 0x10-0x1f
		36, -1, -1, -1, 37, 38, -1, -1, -1, -1, 39, 40, -1, 41, 42, 43,  -- 0x20-0x2f
		0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 44, -1, -1, -1, -1, -1,  -- 0x30-0x3f
		-1, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,  -- 0x40-0x4f
		25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, -1, -1, -1, -1, -1,  -- 0x50-0x5f
	}

	-- Return a binary representation of the numeric string `str`. This must contain only digits 0-9.
	local function encode_string_numeric(str)
		local bitstring = ""
		local int
		string.gsub(str,"..?.?",function(a)
			int = tonumber(a)
			if #a == 3 then
				bitstring = bitstring .. binary(int,10)
			elseif #a == 2 then
				bitstring = bitstring .. binary(int,7)
			else
				bitstring = bitstring .. binary(int,4)
			end
		end)
		return bitstring
	end

	-- Return a binary representation of the alphanumeric string `str`. This must contain only
	-- digits 0-9, uppercase letters A-Z, space and the following chars: $%*./:+-.
	local function encode_string_ascii(str)
		local bitstring = ""
		local int
		local b1, b2
		string.gsub(str,"..?",function(a)
			if #a == 2 then
				b1 = asciitbl[string.byte(string.sub(a,1,1))]
				b2 = asciitbl[string.byte(string.sub(a,2,2))]
				int = b1 * 45 + b2
				bitstring = bitstring .. binary(int,11)
			else
				int = asciitbl[string.byte(a)]
				bitstring = bitstring .. binary(int,6)
			end
		end)
		return bitstring
	end

	-- Return a bitstring representing string str in binary mode.
	-- We don't handle UTF-8 in any special way because we assume the
	-- scanner recognizes UTF-8 and displays it correctly.
	local function encode_string_binary(str)
		local ret = {}
		string.gsub(str,".",function(x)
			ret[#ret + 1] = binary(string.byte(x),8)
		end)
		return table.concat(ret)
	end

	-- Return a bitstring representing string str in the given mode.
	local function encode_data(str,mode)
		if mode == 1 then
			return encode_string_numeric(str)
		elseif mode == 2 then
			return encode_string_ascii(str)
		elseif mode == 4 then
			return encode_string_binary(str)
		else
			assert(false,"not implemented yet")
		end
	end

	-- Encoding the codeword is not enough. We need to make sure that
	-- the length of the binary string is equal to the number of codewords of the version.
	local function add_pad_data(version,ec_level,data)
		local count_to_pad, missing_digits
		local cpty = capacity[version][ec_level] * 8
		count_to_pad = math.min(4,cpty - #data)
		if count_to_pad > 0 then
			data = data .. string.rep("0",count_to_pad)
		end
		if math.fmod(#data,8) ~= 0 then
			missing_digits = 8 - math.fmod(#data,8)
			data = data .. string.rep("0",missing_digits)
		end
		assert(math.fmod(#data,8) == 0)
		-- add "11101100" and "00010001" until enough data
		while #data < cpty do
			data = data .. "11101100"
			if #data < cpty then
				data = data .. "00010001"
			end
		end
		return data
	end



	--- Step 3: Organize data and calculate error correction code
	--- =======================================================
	--- The data in the qrcode is not encoded linearly. For example code 5-H has four blocks, the first two blocks
	--- contain 11 codewords and 22 error correction codes each, the second block contain 12 codewords and 22 ec codes each.
	--- We just take the table from the spec and don't calculate the blocks ourself. The table `ecblocks` contains this info.
	---
	--- During the phase of splitting the data into codewords, we do the calculation for error correction codes. This step involves
	--- polynomial division. Find a math book from school and follow the code here :)

	--- ### Reed Solomon error correction
	--- Now this is the slightly ugly part of the error correction. We start with log/antilog tables
	local alpha_int = {
		[0] = 0,
		2,   4,   8,  16,  32,  64, 128,  29,  58, 116, 232, 205, 135,  19,  38,  76,
		152,  45,  90, 180, 117, 234, 201, 143,   3,   6,  12,  24,  48,  96, 192, 157,
		39,  78, 156,  37,  74, 148,  53, 106, 212, 181, 119, 238, 193, 159,  35,  70,
		140,   5,  10,  20,  40,  80, 160,  93, 186, 105, 210, 185, 111, 222, 161,  95,
		190,  97, 194, 153,  47,  94, 188, 101, 202, 137,  15,  30,  60, 120, 240, 253,
		231, 211, 187, 107, 214, 177, 127, 254, 225, 223, 163,  91, 182, 113, 226, 217,
		175,  67, 134,  17,  34,  68, 136,  13,  26,  52, 104, 208, 189, 103, 206, 129,
		31,  62, 124, 248, 237, 199, 147,  59, 118, 236, 197, 151,  51, 102, 204, 133,
		23,  46,  92, 184, 109, 218, 169,  79, 158,  33,  66, 132,  21,  42,  84, 168,
		77, 154,  41,  82, 164,  85, 170,  73, 146,  57, 114, 228, 213, 183, 115, 230,
		209, 191,  99, 198, 145,  63, 126, 252, 229, 215, 179, 123, 246, 241, 255, 227,
		219, 171,  75, 150,  49,  98, 196, 149,  55, 110, 220, 165,  87, 174,  65, 130,
		25,  50, 100, 200, 141,   7,  14,  28,  56, 112, 224, 221, 167,  83, 166,  81,
		162,  89, 178, 121, 242, 249, 239, 195, 155,  43,  86, 172,  69, 138,   9,  18,
		36,  72, 144,  61, 122, 244, 245, 247, 243, 251, 235, 203, 139,  11,  22,  44,
		88, 176, 125, 250, 233, 207, 131,  27,  54, 108, 216, 173,  71, 142,   1
	}

	local int_alpha = {
		[0] = 0,
		255,   1,  25,   2,  50,  26, 198,   3, 223,  51, 238,  27, 104, 199,  75,   4,
		100, 224,  14,  52, 141, 239, 129,  28, 193, 105, 248, 200,   8,  76, 113,   5,
		138, 101,  47, 225,  36,  15,  33,  53, 147, 142, 218, 240,  18, 130,  69,  29,
		181, 194, 125, 106,  39, 249, 185, 201, 154,   9, 120,  77, 228, 114, 166,   6,
		191, 139,  98, 102, 221,  48, 253, 226, 152,  37, 179,  16, 145,  34, 136,  54,
		208, 148, 206, 143, 150, 219, 189, 241, 210,  19,  92, 131,  56,  70,  64,  30,
		66, 182, 163, 195,  72, 126, 110, 107,  58,  40,  84, 250, 133, 186,  61, 202,
		94, 155, 159,  10,  21, 121,  43,  78, 212, 229, 172, 115, 243, 167,  87,   7,
		112, 192, 247, 140, 128,  99,  13, 103,  74, 222, 237,  49, 197, 254,  24, 227,
		165, 153, 119,  38, 184, 180, 124,  17,  68, 146, 217,  35,  32, 137,  46,  55,
		63, 209,  91, 149, 188, 207, 205, 144, 135, 151, 178, 220, 252, 190,  97, 242,
		86, 211, 171,  20,  42,  93, 158, 132,  60,  57,  83,  71, 109,  65, 162,  31,
		45,  67, 216, 183, 123, 164, 118, 196,  23,  73, 236, 127,  12, 111, 246, 108,
		161,  59,  82,  41, 157,  85, 170, 251,  96, 134, 177, 187, 204,  62,  90, 203,
		89,  95, 176, 156, 169, 160,  81,  11, 245,  22, 235, 122, 117,  44, 215,  79,
		174, 213, 233, 230, 231, 173, 232, 116, 214, 244, 234, 168,  80,  88, 175
	}

	-- We only need the polynomial generators for block sizes 7, 10, 13, 15, 16, 17, 18, 20, 22, 24, 26, 28, and 30. Version
	-- 2 of the qr codes don't need larger ones (as opposed to version 1). The table has the format x^1*ɑ^21 + x^2*a^102 ...
	local generator_polynomial = {
		[7] = { 21, 102, 238, 149, 146, 229,  87,   0},
		[10] = { 45,  32,  94,  64,  70, 118,  61,  46,  67, 251,   0 },
		[13] = { 78, 140, 206, 218, 130, 104, 106, 100,  86, 100, 176, 152,  74,   0 },
		[15] = {105,  99,   5, 124, 140, 237,  58,  58,  51,  37, 202,  91,  61, 183,   8,   0},
		[16] = {120, 225, 194, 182, 169, 147, 191,  91,   3,  76, 161, 102, 109, 107, 104, 120,   0},
		[17] = {136, 163, 243,  39, 150,  99,  24, 147, 214, 206, 123, 239,  43,  78, 206, 139,  43,   0},
		[18] = {153,  96,  98,   5, 179, 252, 148, 152, 187,  79, 170, 118,  97, 184,  94, 158, 234, 215,   0},
		[20] = {190, 188, 212, 212, 164, 156, 239,  83, 225, 221, 180, 202, 187,  26, 163,  61,  50,  79,  60,  17,   0},
		[22] = {231, 165, 105, 160, 134, 219,  80,  98, 172,   8,  74, 200,  53, 221, 109,  14, 230,  93, 242, 247, 171, 210,   0},
		[24] = { 21, 227,  96,  87, 232, 117,   0, 111, 218, 228, 226, 192, 152, 169, 180, 159, 126, 251, 117, 211,  48, 135, 121, 229,   0},
		[26] = { 70, 218, 145, 153, 227,  48, 102,  13, 142, 245,  21, 161,  53, 165,  28, 111, 201, 145,  17, 118, 182, 103,   2, 158, 125, 173,   0},
		[28] = {123,   9,  37, 242, 119, 212, 195,  42,  87, 245,  43,  21, 201, 232,  27, 205, 147, 195, 190, 110, 180, 108, 234, 224, 104, 200, 223, 168,   0},
		[30] = {180, 192,  40, 238, 216, 251,  37, 156, 130, 224, 193, 226, 173,  42, 125, 222,  96, 239,  86, 110,  48,  50, 182, 179,  31, 216, 152, 145, 173, 41, 0}}


	-- Turn a binary string of length 8*x into a table size x of numbers.
	local function convert_bitstring_to_bytes(data)
		local msg = {}
		local tab = string.gsub(data,"(........)",function(x)
			msg[#msg+1] = tonumber(x,2)
			end)
		return msg
	end

	-- Return a table that has 0's in the first entries and then the alpha
	-- representation of the generator polynominal
	local function get_generator_polynominal_adjusted(num_ec_codewords,highest_exponent)
		local gp_alpha = {[0]=0}
		for i=0,highest_exponent - num_ec_codewords - 1 do
			gp_alpha[i] = 0
		end
		local gp = generator_polynomial[num_ec_codewords]
		for i=1,num_ec_codewords + 1 do
			gp_alpha[highest_exponent - num_ec_codewords + i - 1] = gp[i]
		end
		return gp_alpha
	end

	--- These converter functions use the log/antilog table above.
	--- We could have created the table programatically, but I like fixed tables.
	-- Convert polynominal in int notation to alpha notation.
	local function convert_to_alpha( tab )
		local new_tab = {}
		for i=0,#tab do
			new_tab[i] = int_alpha[tab[i]]
		end
		return new_tab
	end

	-- Convert polynominal in alpha notation to int notation.
	local function convert_to_int(tab,len_message)
		local new_tab = {}
		for i=0,#tab do
			new_tab[i] = alpha_int[tab[i]]
		end
		return new_tab
	end

	-- That's the heart of the error correction calculation.
	local function calculate_error_correction(data,num_ec_codewords)
		local mp
		if type(data)=="string" then
			mp = convert_bitstring_to_bytes(data)
		elseif type(data)=="table" then
			mp = data
		else
			assert(false,"Unknown type for data: %s",type(data))
		end
		local len_message = #mp

		local highest_exponent = len_message + num_ec_codewords - 1
		local gp_alpha,tmp
		local he
		local gp_int = {}
		local mp_int,mp_alpha = {},{}
		-- create message shifted to left (highest exponent)
		for i=1,len_message do
			mp_int[highest_exponent - i + 1] = mp[i]
		end
		for i=1,highest_exponent - len_message do
			mp_int[i] = 0
		end
		mp_int[0] = 0

		mp_alpha = convert_to_alpha(mp_int)

		while highest_exponent >= num_ec_codewords do
			gp_alpha = get_generator_polynominal_adjusted(num_ec_codewords,highest_exponent)

			-- Multiply generator polynomial by first coefficient of the above polynomial

			-- take the highest exponent from the message polynom (alpha) and add
			-- it to the generator polynom
			local exp = mp_alpha[highest_exponent]
			for i=highest_exponent,highest_exponent - num_ec_codewords,-1 do
				if gp_alpha[i] + exp > 255 then
					gp_alpha[i] = math.fmod(gp_alpha[i] + exp,255)
				else
					gp_alpha[i] = gp_alpha[i] + exp
				end
			end
			for i=highest_exponent - num_ec_codewords - 1,0,-1 do
				gp_alpha[i] = 0
			end

			gp_int = convert_to_int(gp_alpha)
			mp_int = convert_to_int(mp_alpha)


			tmp = {}
			for i=highest_exponent,0,-1 do
				tmp[i] = bit_xor(gp_int[i],mp_int[i])
			end
			-- remove leading 0's
			he = highest_exponent
			for i=he,0,-1 do
				-- We need to stop if the length of the codeword is matched
				if i < num_ec_codewords then break end
				if tmp[i] == 0 then
					tmp[i] = nil
					highest_exponent = highest_exponent - 1
				else
					break
				end
			end
			mp_int = tmp
			mp_alpha = convert_to_alpha(mp_int)
		end
		local ret = {}

		-- reverse data
		for i=#mp_int,0,-1 do
			ret[#ret + 1] = mp_int[i]
		end
		return ret
	end

	--- #### Arranging the data
	--- Now we arrange the data into smaller chunks. This table is taken from the spec.
	-- ecblocks has 40 entries, one for each version. Each version entry has 4 entries, for each LMQH
	-- ec level. Each entry has two or four fields, the odd files are the number of repetitions for the
	-- folowing block info. The first entry of the block is the total number of codewords in the block,
	-- the second entry is the number of data codewords. The third is not important.
	local ecblocks = {
	{{  1,{ 26, 19, 2}                 },   {  1,{26,16, 4}},                  {  1,{26,13, 6}},                  {  1, {26, 9, 8}               }},
	{{  1,{ 44, 34, 4}                 },   {  1,{44,28, 8}},                  {  1,{44,22,11}},                  {  1, {44,16,14}               }},
	{{  1,{ 70, 55, 7}                 },   {  1,{70,44,13}},                  {  2,{35,17, 9}},                  {  2, {35,13,11}               }},
	{{  1,{100, 80,10}                 },   {  2,{50,32, 9}},                  {  2,{50,24,13}},                  {  4, {25, 9, 8}               }},
	{{  1,{134,108,13}                 },   {  2,{67,43,12}},                  {  2,{33,15, 9},  2,{34,16, 9}},   {  2, {33,11,11},  2,{34,12,11}}},
	{{  2,{ 86, 68, 9}                 },   {  4,{43,27, 8}},                  {  4,{43,19,12}},                  {  4, {43,15,14}               }},
	{{  2,{ 98, 78,10}                 },   {  4,{49,31, 9}},                  {  2,{32,14, 9},  4,{33,15, 9}},   {  4, {39,13,13},  1,{40,14,13}}},
	{{  2,{121, 97,12}                 },   {  2,{60,38,11},  2,{61,39,11}},   {  4,{40,18,11},  2,{41,19,11}},   {  4, {40,14,13},  2,{41,15,13}}},
	{{  2,{146,116,15}                 },   {  3,{58,36,11},  2,{59,37,11}},   {  4,{36,16,10},  4,{37,17,10}},   {  4, {36,12,12},  4,{37,13,12}}},
	{{  2,{ 86, 68, 9},  2,{ 87, 69, 9}},   {  4,{69,43,13},  1,{70,44,13}},   {  6,{43,19,12},  2,{44,20,12}},   {  6, {43,15,14},  2,{44,16,14}}},
	{{  4,{101, 81,10}                 },   {  1,{80,50,15},  4,{81,51,15}},   {  4,{50,22,14},  4,{51,23,14}},   {  3, {36,12,12},  8,{37,13,12}}},
	{{  2,{116, 92,12},  2,{117, 93,12}},   {  6,{58,36,11},  2,{59,37,11}},   {  4,{46,20,13},  6,{47,21,13}},   {  7, {42,14,14},  4,{43,15,14}}},
	{{  4,{133,107,13}                 },   {  8,{59,37,11},  1,{60,38,11}},   {  8,{44,20,12},  4,{45,21,12}},   { 12, {33,11,11},  4,{34,12,11}}},
	{{  3,{145,115,15},  1,{146,116,15}},   {  4,{64,40,12},  5,{65,41,12}},   { 11,{36,16,10},  5,{37,17,10}},   { 11, {36,12,12},  5,{37,13,12}}},
	{{  5,{109, 87,11},  1,{110, 88,11}},   {  5,{65,41,12},  5,{66,42,12}},   {  5,{54,24,15},  7,{55,25,15}},   { 11, {36,12,12},  7,{37,13,12}}},
	{{  5,{122, 98,12},  1,{123, 99,12}},   {  7,{73,45,14},  3,{74,46,14}},   { 15,{43,19,12},  2,{44,20,12}},   {  3, {45,15,15}, 13,{46,16,15}}},
	{{  1,{135,107,14},  5,{136,108,14}},   { 10,{74,46,14},  1,{75,47,14}},   {  1,{50,22,14}, 15,{51,23,14}},   {  2, {42,14,14}, 17,{43,15,14}}},
	{{  5,{150,120,15},  1,{151,121,15}},   {  9,{69,43,13},  4,{70,44,13}},   { 17,{50,22,14},  1,{51,23,14}},   {  2, {42,14,14}, 19,{43,15,14}}},
	{{  3,{141,113,14},  4,{142,114,14}},   {  3,{70,44,13}, 11,{71,45,13}},   { 17,{47,21,13},  4,{48,22,13}},   {  9, {39,13,13}, 16,{40,14,13}}},
	{{  3,{135,107,14},  5,{136,108,14}},   {  3,{67,41,13}, 13,{68,42,13}},   { 15,{54,24,15},  5,{55,25,15}},   { 15, {43,15,14}, 10,{44,16,14}}},
	{{  4,{144,116,14},  4,{145,117,14}},   { 17,{68,42,13}},                  { 17,{50,22,14},  6,{51,23,14}},   { 19, {46,16,15},  6,{47,17,15}}},
	{{  2,{139,111,14},  7,{140,112,14}},   { 17,{74,46,14}},                  {  7,{54,24,15}, 16,{55,25,15}},   { 34, {37,13,12}               }},
	{{  4,{151,121,15},  5,{152,122,15}},   {  4,{75,47,14}, 14,{76,48,14}},   { 11,{54,24,15}, 14,{55,25,15}},   { 16, {45,15,15}, 14,{46,16,15}}},
	{{  6,{147,117,15},  4,{148,118,15}},   {  6,{73,45,14}, 14,{74,46,14}},   { 11,{54,24,15}, 16,{55,25,15}},   { 30, {46,16,15},  2,{47,17,15}}},
	{{  8,{132,106,13},  4,{133,107,13}},   {  8,{75,47,14}, 13,{76,48,14}},   {  7,{54,24,15}, 22,{55,25,15}},   { 22, {45,15,15}, 13,{46,16,15}}},
	{{ 10,{142,114,14},  2,{143,115,14}},   { 19,{74,46,14},  4,{75,47,14}},   { 28,{50,22,14},  6,{51,23,14}},   { 33, {46,16,15},  4,{47,17,15}}},
	{{  8,{152,122,15},  4,{153,123,15}},   { 22,{73,45,14},  3,{74,46,14}},   {  8,{53,23,15}, 26,{54,24,15}},   { 12, {45,15,15}, 28,{46,16,15}}},
	{{  3,{147,117,15}, 10,{148,118,15}},   {  3,{73,45,14}, 23,{74,46,14}},   {  4,{54,24,15}, 31,{55,25,15}},   { 11, {45,15,15}, 31,{46,16,15}}},
	{{  7,{146,116,15},  7,{147,117,15}},   { 21,{73,45,14},  7,{74,46,14}},   {  1,{53,23,15}, 37,{54,24,15}},   { 19, {45,15,15}, 26,{46,16,15}}},
	{{  5,{145,115,15}, 10,{146,116,15}},   { 19,{75,47,14}, 10,{76,48,14}},   { 15,{54,24,15}, 25,{55,25,15}},   { 23, {45,15,15}, 25,{46,16,15}}},
	{{ 13,{145,115,15},  3,{146,116,15}},   {  2,{74,46,14}, 29,{75,47,14}},   { 42,{54,24,15},  1,{55,25,15}},   { 23, {45,15,15}, 28,{46,16,15}}},
	{{ 17,{145,115,15}            	 },   { 10,{74,46,14}, 23,{75,47,14}},   { 10,{54,24,15}, 35,{55,25,15}},   { 19, {45,15,15}, 35,{46,16,15}}},
	{{ 17,{145,115,15},  1,{146,116,15}},   { 14,{74,46,14}, 21,{75,47,14}},   { 29,{54,24,15}, 19,{55,25,15}},   { 11, {45,15,15}, 46,{46,16,15}}},
	{{ 13,{145,115,15},  6,{146,116,15}},   { 14,{74,46,14}, 23,{75,47,14}},   { 44,{54,24,15},  7,{55,25,15}},   { 59, {46,16,15},  1,{47,17,15}}},
	{{ 12,{151,121,15},  7,{152,122,15}},   { 12,{75,47,14}, 26,{76,48,14}},   { 39,{54,24,15}, 14,{55,25,15}},   { 22, {45,15,15}, 41,{46,16,15}}},
	{{  6,{151,121,15}, 14,{152,122,15}},   {  6,{75,47,14}, 34,{76,48,14}},   { 46,{54,24,15}, 10,{55,25,15}},   {  2, {45,15,15}, 64,{46,16,15}}},
	{{ 17,{152,122,15},  4,{153,123,15}},   { 29,{74,46,14}, 14,{75,47,14}},   { 49,{54,24,15}, 10,{55,25,15}},   { 24, {45,15,15}, 46,{46,16,15}}},
	{{  4,{152,122,15}, 18,{153,123,15}},   { 13,{74,46,14}, 32,{75,47,14}},   { 48,{54,24,15}, 14,{55,25,15}},   { 42, {45,15,15}, 32,{46,16,15}}},
	{{ 20,{147,117,15},  4,{148,118,15}},   { 40,{75,47,14},  7,{76,48,14}},   { 43,{54,24,15}, 22,{55,25,15}},   { 10, {45,15,15}, 67,{46,16,15}}},
	{{ 19,{148,118,15},  6,{149,119,15}},   { 18,{75,47,14}, 31,{76,48,14}},   { 34,{54,24,15}, 34,{55,25,15}},   { 20, {45,15,15}, 61,{46,16,15}}}
	}

	-- The bits that must be 0 if the version does fill the complete matrix.
	-- Example: for version 1, no bits need to be added after arranging the data, for version 2 we need to add 7 bits at the end.
	local remainder = {0, 7, 7, 7, 7, 7, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 0, 0, 0, 0, 0, 0}

	-- This is the formula for table 1 in the spec:
	-- function get_capacity_remainder( version )
	-- 	local len = version * 4 + 17
	-- 	local size = len^2
	-- 	local function_pattern_modules = 192 + 2 * len - 32 -- Position Adjustment pattern + timing pattern
	-- 	local count_alignemnt_pattern = #alignment_pattern[version]
	-- 	if count_alignemnt_pattern > 0 then
	-- 		-- add 25 for each aligment pattern
	-- 		function_pattern_modules = function_pattern_modules + 25 * ( count_alignemnt_pattern^2 - 3 )
	-- 		-- but substract the timing pattern occupied by the aligment pattern on the top and left
	-- 		function_pattern_modules = function_pattern_modules - ( count_alignemnt_pattern - 2) * 10
	-- 	end
	-- 	size = size - function_pattern_modules
	-- 	if version > 6 then
	-- 		size = size - 67
	-- 	else
	-- 		size = size - 31
	-- 	end
	-- 	return math.floor(size/8),math.fmod(size,8)
	-- end


	--- Example: Version 5-H has four data and four error correction blocks. The table above lists
	--- `2, {33,11,11},  2,{34,12,11}` for entry [5][4]. This means we take two blocks with 11 codewords
	--- and two blocks with 12 codewords, and two blocks with 33 - 11 = 22 ec codes and another
	--- two blocks with 34 - 12 = 22 ec codes.
	---	     Block 1: D1  D2  D3  ... D11
	---	     Block 2: D12 D13 D14 ... D22
	---	     Block 3: D23 D24 D25 ... D33 D34
	---	     Block 4: D35 D36 D37 ... D45 D46
	--- Then we place the data like this in the matrix: D1, D12, D23, D35, D2, D13, D24, D36 ... D45, D34, D46.  The same goes
	--- with error correction codes.

	-- The given data can be a string of 0's and 1' (with #string mod 8 == 0).
	-- Alternatively the data can be a table of codewords. The number of codewords
	-- must match the capacity of the qr code.
	local function arrange_codewords_and_calculate_ec( version,ec_level,data )
		if type(data)=="table" then
			local tmp = ""
			for i=1,#data do
				tmp = tmp .. binary(data[i],8)
			end
			data = tmp
		end
		-- If the size of the data is not enough for the codeword, we add 0's and two special bytes until finished.
		local blocks = ecblocks[version][ec_level]
		local size_datablock_bytes, size_ecblock_bytes
		local datablocks = {}
		local ecblocks = {}
		local count = 1
		local pos = 0
		local cpty_ec_bits = 0
		for i=1,#blocks/2 do
			for j=1,blocks[2*i - 1] do
				size_datablock_bytes = blocks[2*i][2]
				size_ecblock_bytes   = blocks[2*i][1] - blocks[2*i][2]
				cpty_ec_bits = cpty_ec_bits + size_ecblock_bytes * 8
				datablocks[#datablocks + 1] = string.sub(data, pos * 8 + 1,( pos + size_datablock_bytes)*8)
				tmp_tab = calculate_error_correction(datablocks[#datablocks],size_ecblock_bytes)
				tmp_str = ""
				for x=1,#tmp_tab do
					tmp_str = tmp_str .. binary(tmp_tab[x],8)
				end
				ecblocks[#ecblocks + 1] = tmp_str
				pos = pos + size_datablock_bytes
				count = count + 1
			end
		end
		local arranged_data = ""
		pos = 1
		repeat
			for i=1,#datablocks do
				if pos < #datablocks[i] then
					arranged_data = arranged_data .. string.sub(datablocks[i],pos, pos + 7)
				end
			end
			pos = pos + 8
		until #arranged_data == #data
		-- ec
		local arranged_ec = ""
		pos = 1
		repeat
			for i=1,#ecblocks do
				if pos < #ecblocks[i] then
					arranged_ec = arranged_ec .. string.sub(ecblocks[i],pos, pos + 7)
				end
			end
			pos = pos + 8
		until #arranged_ec == cpty_ec_bits
		return arranged_data .. arranged_ec
	end

	--- Step 4: Generate 8 matrices with different masks and calculate the penalty
	--- ==========================================================================
	---
	--- Prepare matrix
	--- --------------
	--- The first step is to prepare an _empty_ matrix for a given size/mask. The matrix has a
	--- few predefined areas that must be black or blank. We encode the matrix with a two
	--- dimensional field where the numbers determine which pixel is blank or not.
	---
	--- The following code is used for our matrix:
	---	     0 = not in use yet,
	---	    -2 = blank by mandatory pattern,
	---	     2 = black by mandatory pattern,
	---	    -1 = blank by data,
	---	     1 = black by data
	---
	---
	--- To prepare the _empty_, we add positioning, alingment and timing patters.

	--- ### Positioning patterns ###
	local function add_position_detection_patterns(tab_x)
		local size = #tab_x
		-- allocate quite zone in the matrix area
		for i=1,8 do
			for j=1,8 do
				tab_x[i][j] = -2
				tab_x[size - 8 + i][j] = -2
				tab_x[i][size - 8 + j] = -2
			end
		end
		-- draw the detection pattern (outer)
		for i=1,7 do
			-- top left
			tab_x[1][i]=2
			tab_x[7][i]=2
			tab_x[i][1]=2
			tab_x[i][7]=2

			-- top right
			tab_x[size][i]=2
			tab_x[size - 6][i]=2
			tab_x[size - i + 1][1]=2
			tab_x[size - i + 1][7]=2

			-- bottom left
			tab_x[1][size - i + 1]=2
			tab_x[7][size - i + 1]=2
			tab_x[i][size - 6]=2
			tab_x[i][size]=2
		end
		-- draw the detection pattern (inner)
		for i=1,3 do
			for j=1,3 do
				-- top left
				tab_x[2+j][i+2]=2
				-- top right
				tab_x[size - j - 1][i+2]=2
				-- bottom left
				tab_x[2 + j][size - i - 1]=2
			end
		end
	end

	--- ### Timing patterns ###
	-- The timing patterns (two) are the dashed lines between two adjacent positioning patterns on row/column 7.
	local function add_timing_pattern(tab_x)
		local line,col
		line = 7
		col = 9
		for i=col,#tab_x - 8 do
			if math.fmod(i,2) == 1 then
				tab_x[i][line] = 2
			else
				tab_x[i][line] = -2
			end
		end
		for i=col,#tab_x - 8 do
			if math.fmod(i,2) == 1 then
				tab_x[line][i] = 2
			else
				tab_x[line][i] = -2
			end
		end
	end


	--- ### Alignment patterns ###
	--- The alignment patterns must be added to the matrix for versions > 1. The amount and positions depend on the versions and are
	--- given by the spec. Beware: the patterns must not be placed where we have the positioning patterns
	--- (that is: top left, top right and bottom left.)

	-- For each version, where should we place the alignment patterns? See table E.1 of the spec
	local alignment_pattern = {
	{},{6,18},{6,22},{6,26},{6,30},{6,34}, -- 1-6
	{6,22,38},{6,24,42},{6,26,46},{6,28,50},{6,30,54},{6,32,58},{6,34,62}, -- 7-13
	{6,26,46,66},{6,26,48,70},{6,26,50,74},{6,30,54,78},{6,30,56,82},{6,30,58,86},{6,34,62,90}, -- 14-20
	{6,28,50,72,94},{6,26,50,74,98},{6,30,54,78,102},{6,28,54,80,106},{6,32,58,84,110},{6,30,58,86,114},{6,34,62,90,118}, -- 21-27
	{6,26,50,74,98 ,122},{6,30,54,78,102,126},{6,26,52,78,104,130},{6,30,56,82,108,134},{6,34,60,86,112,138},{6,30,58,86,114,142},{6,34,62,90,118,146}, -- 28-34
	{6,30,54,78,102,126,150}, {6,24,50,76,102,128,154},{6,28,54,80,106,132,158},{6,32,58,84,110,136,162},{6,26,54,82,110,138,166},{6,30,58,86,114,142,170} -- 35 - 40
	}

	--- The alignment pattern has size 5x5 and looks like this:
	---     XXXXX
	---     X   X
	---     X X X
	---     X   X
	---     XXXXX
	local function add_alignment_pattern( tab_x )
		local version = (#tab_x - 17) / 4
		local ap = alignment_pattern[version]
		local pos_x, pos_y
		for x=1,#ap do
			for y=1,#ap do
				-- we must not put an alignment pattern on top of the positioning pattern
				if not (x == 1 and y == 1 or x == #ap and y == 1 or x == 1 and y == #ap ) then
					pos_x = ap[x] + 1
					pos_y = ap[y] + 1
					tab_x[pos_x][pos_y] = 2
					tab_x[pos_x+1][pos_y] = -2
					tab_x[pos_x-1][pos_y] = -2
					tab_x[pos_x+2][pos_y] =  2
					tab_x[pos_x-2][pos_y] =  2
					tab_x[pos_x  ][pos_y - 2] = 2
					tab_x[pos_x+1][pos_y - 2] = 2
					tab_x[pos_x-1][pos_y - 2] = 2
					tab_x[pos_x+2][pos_y - 2] = 2
					tab_x[pos_x-2][pos_y - 2] = 2
					tab_x[pos_x  ][pos_y + 2] = 2
					tab_x[pos_x+1][pos_y + 2] = 2
					tab_x[pos_x-1][pos_y + 2] = 2
					tab_x[pos_x+2][pos_y + 2] = 2
					tab_x[pos_x-2][pos_y + 2] = 2

					tab_x[pos_x  ][pos_y - 1] = -2
					tab_x[pos_x+1][pos_y - 1] = -2
					tab_x[pos_x-1][pos_y - 1] = -2
					tab_x[pos_x+2][pos_y - 1] =  2
					tab_x[pos_x-2][pos_y - 1] =  2
					tab_x[pos_x  ][pos_y + 1] = -2
					tab_x[pos_x+1][pos_y + 1] = -2
					tab_x[pos_x-1][pos_y + 1] = -2
					tab_x[pos_x+2][pos_y + 1] =  2
					tab_x[pos_x-2][pos_y + 1] =  2
				end
			end
		end
	end

	--- ### Type information ###
	--- Let's not forget the type information that is in column 9 next to the left positioning patterns and on row 9 below
	--- the top positioning patterns. This type information is not fixed, it depends on the mask and the error correction.

	-- The first index is ec level (LMQH,1-4), the second is the mask (0-7). This bitstring of length 15 is to be used
	-- as mandatory pattern in the qrcode. Mask -1 is for debugging purpose only and is the 'noop' mask.
	local typeinfo = {
		{ [-1]= "111111111111111", [0] = "111011111000100", "111001011110011", "111110110101010", "111100010011101", "110011000101111", "110001100011000", "110110001000001", "110100101110110" },
		{ [-1]= "111111111111111", [0] = "101010000010010", "101000100100101", "101111001111100", "101101101001011", "100010111111001", "100000011001110", "100111110010111", "100101010100000" },
		{ [-1]= "111111111111111", [0] = "011010101011111", "011000001101000", "011111100110001", "011101000000110", "010010010110100", "010000110000011", "010111011011010", "010101111101101" },
		{ [-1]= "111111111111111", [0] = "001011010001001", "001001110111110", "001110011100111", "001100111010000", "000011101100010", "000001001010101", "000110100001100", "000100000111011" }
	}

	-- The typeinfo is a mixture of mask and ec level information and is
	-- added twice to the qr code, one horizontal, one vertical.
	local function add_typeinfo_to_matrix( matrix,ec_level,mask )
		local ec_mask_type = typeinfo[ec_level][mask]

		local bit
		-- vertical from bottom to top
		for i=1,7 do
			bit = string.sub(ec_mask_type,i,i)
			fill_matrix_position(matrix, bit, 9, #matrix - i + 1)
		end
		for i=8,9 do
			bit = string.sub(ec_mask_type,i,i)
			fill_matrix_position(matrix,bit,9,17-i)
		end
		for i=10,15 do
			bit = string.sub(ec_mask_type,i,i)
			fill_matrix_position(matrix,bit,9,16 - i)
		end
		-- horizontal, left to right
		for i=1,6 do
			bit = string.sub(ec_mask_type,i,i)
			fill_matrix_position(matrix,bit,i,9)
		end
		bit = string.sub(ec_mask_type,7,7)
		fill_matrix_position(matrix,bit,8,9)
		for i=8,15 do
			bit = string.sub(ec_mask_type,i,i)
			fill_matrix_position(matrix,bit,#matrix - 15 + i,9)
		end
	end

	-- Bits for version information 7-40
	local version_information = {"001010010011111000", "000111101101000100", "100110010101100100","011001011001010100",
	"011011111101110100", "001000110111001100", "111000100001101100", "010110000011011100", "000101001001111100",
	"000111101101000010", "010111010001100010", "111010000101010010", "001001100101110010", "011001011001001010",
	"011000001011101010", "100100110001011010", "000110111111111010", "001000110111000110", "000100001111100110",
	"110101011111010110", "000001110001110110", "010110000011001110", "001111110011101110", "101011101011011110",
	"000000101001111110", "101010111001000001", "000001111011100001", "010111010001010001", "011111001111110001",
	"110100001101001001", "001110100001101001", "001001100101011001", "010000010101111001", "100101100011000101" }

	-- Versions 7 and above need two bitfields with version information added to the code
	local function add_version_information(matrix,version)
		if version < 7 then return end
		local size = #matrix
		local bitstring = version_information[version - 6]
		local x,y, bit
		local start_x, start_y
		-- first top right
		start_x = #matrix - 10
		start_y = 1
		for i=1,#bitstring do
			bit = string.sub(bitstring,i,i)
			x = start_x + math.fmod(i - 1,3)
			y = start_y + math.floor( (i - 1) / 3 )
			fill_matrix_position(matrix,bit,x,y)
		end

		-- now bottom left
		start_x = 1
		start_y = #matrix - 10
		for i=1,#bitstring do
			bit = string.sub(bitstring,i,i)
			x = start_x + math.floor( (i - 1) / 3 )
			y = start_y + math.fmod(i - 1,3)
			fill_matrix_position(matrix,bit,x,y)
		end
	end

	--- Now it's time to use the methods above to create a prefilled matrix for the given mask
	local function prepare_matrix_with_mask( version,ec_level, mask )
		local size
		local tab_x = {}

		size = version * 4 + 17
		for i=1,size do
			tab_x[i]={}
			for j=1,size do
				tab_x[i][j] = 0
			end
		end
		add_position_detection_patterns(tab_x)
		add_timing_pattern(tab_x)
		add_version_information(tab_x,version)

		-- black pixel above lower left position detection pattern
		tab_x[9][size - 7] = 2
		add_alignment_pattern(tab_x)
		add_typeinfo_to_matrix(tab_x,ec_level, mask)
		return tab_x
	end

	--- Finally we come to the place where we need to put the calculated data (remember step 3?) into the qr code.
	--- We do this for each mask. BTW speaking of mask, this is what we find in the spec:
	---	     Mask Pattern Reference   Condition
	---	     000                      (y + x) mod 2 = 0
	---	     001                      y mod 2 = 0
	---	     010                      x mod 3 = 0
	---	     011                      (y + x) mod 3 = 0
	---	     100                      ((y div 2) + (x div 3)) mod 2 = 0
	---	     101                      (y x) mod 2 + (y x) mod 3 = 0
	---	     110                      ((y x) mod 2 + (y x) mod 3) mod 2 = 0
	---	     111                      ((y x) mod 3 + (y+x) mod 2) mod 2 = 0

	-- Return 1 (black) or -1 (blank) depending on the mask, value and position.
	-- Parameter mask is 0-7 (-1 for 'no mask'). x and y are 1-based coordinates,
	-- 1,1 = upper left. tonumber(value) must be 0 or 1.
	local function get_pixel_with_mask( mask, x,y,value )
		x = x - 1
		y = y - 1
		local invert = false
		-- test purpose only:
		if mask == -1 then
			-- ignore, no masking applied
		elseif mask == 0 then
			if math.fmod(x + y,2) == 0 then invert = true end
		elseif mask == 1 then
			if math.fmod(y,2) == 0 then invert = true end
		elseif mask == 2 then
			if math.fmod(x,3) == 0 then invert = true end
		elseif mask == 3 then
			if math.fmod(x + y,3) == 0 then invert = true end
		elseif mask == 4 then
			if math.fmod(math.floor(y / 2) + math.floor(x / 3),2) == 0 then invert = true end
		elseif mask == 5 then
			if math.fmod(x * y,2) + math.fmod(x * y,3) == 0 then invert = true end
		elseif mask == 6 then
			if math.fmod(math.fmod(x * y,2) + math.fmod(x * y,3),2) == 0 then invert = true end
		elseif mask == 7 then
			if math.fmod(math.fmod(x * y,3) + math.fmod(x + y,2),2) == 0 then invert = true end
		else
			assert(false,"This can't happen (mask must be <= 7)")
		end
		if invert then
			-- value = 1? -> -1, value = 0? -> 1
			return 1 - 2 * tonumber(value)
		else
			-- value = 1? -> 1, value = 0? -> -1
			return -1 + 2*tonumber(value)
		end
	end


	-- We need up to 8 positions in the matrix. Only the last few bits may be less then 8.
	-- The function returns a table of (up to) 8 entries with subtables where
	-- the x coordinate is the first and the y coordinate is the second entry.
	local function get_next_free_positions(matrix,x,y,dir,byte)
		local ret = {}
		local count = 1
		local mode = "right"
		while count <= #byte do
			if mode == "right" and matrix[x][y] == 0 then
				ret[#ret + 1] = {x,y}
				mode = "left"
				count = count + 1
			elseif mode == "left" and matrix[x-1][y] == 0 then
				ret[#ret + 1] = {x-1,y}
				mode = "right"
				count = count + 1
				if dir == "up" then
					y = y - 1
				else
					y = y + 1
				end
			elseif mode == "right" and matrix[x-1][y] == 0 then
				ret[#ret + 1] = {x-1,y}
				count = count + 1
				if dir == "up" then
					y = y - 1
				else
					y = y + 1
				end
			else
				if dir == "up" then
					y = y - 1
				else
					y = y + 1
				end
			end
			if y < 1 or y > #matrix then
				x = x - 2
				-- don't overwrite the timing pattern
				if x == 7 then x = 6 end
				if dir == "up" then
					dir = "down"
					y = 1
				else
					dir = "up"
					y = #matrix
				end
			end
		end
		return ret,x,y,dir
	end

	-- Add the data string (0's and 1's) to the matrix for the given mask.
	local function add_data_to_matrix(matrix,data,mask)
		size = #matrix
		local x,y,positions
		local _x,_y,m
		local dir = "up"
		local byte_number = 0
		x,y = size,size
		string.gsub(data,".?.?.?.?.?.?.?.?",function ( byte )
			byte_number = byte_number + 1
			positions,x,y,dir = get_next_free_positions(matrix,x,y,dir,byte,mask)
			for i=1,#byte do
				_x = positions[i][1]
				_y = positions[i][2]
				m = get_pixel_with_mask(mask,_x,_y,string.sub(byte,i,i))
				if debugging then
					matrix[_x][_y] = m * (i + 10)
				else
					matrix[_x][_y] = m
				end
			end
		end)
	end


	--- The total penalty of the matrix is the sum of four steps. The following steps are taken into account:
	---
	--- 1. Adjacent modules in row/column in same color
	--- 1. Block of modules in same color
	--- 1. 1:1:3:1:1 ratio (dark:light:dark:light:dark) pattern in row/column
	--- 1. Proportion of dark modules in entire symbol
	---
	--- This all is done to avoid bad patterns in the code that prevent the scanner from
	--- reading the code.
	-- Return the penalty for the given matrix
	local function calculate_penalty(matrix)
		local penalty1, penalty2, penalty3, penalty4 = 0,0,0,0
		local size = #matrix
		-- this is for penalty 4
		local number_of_dark_cells = 0

		-- 1: Adjacent modules in row/column in same color
		-- --------------------------------------------
		-- No. of modules = (5+i)  -> 3 + i
		local last_bit_blank -- < 0:  blank, > 0: black
		local is_blank
		local number_of_consecutive_bits
		-- first: vertical
		for x=1,size do
			number_of_consecutive_bits = 0
			last_bit_blank = nil
			for y = 1,size do
				if matrix[x][y] > 0 then
					-- small optimization: this is for penalty 4
					number_of_dark_cells = number_of_dark_cells + 1
					is_blank = false
				else
					is_blank = true
				end
				is_blank = matrix[x][y] < 0
				if last_bit_blank == is_blank then
					number_of_consecutive_bits = number_of_consecutive_bits + 1
				else
					if number_of_consecutive_bits >= 5 then
						penalty1 = penalty1 + number_of_consecutive_bits - 2
					end
					number_of_consecutive_bits = 1
				end
				last_bit_blank = is_blank
			end
			if number_of_consecutive_bits >= 5 then
				penalty1 = penalty1 + number_of_consecutive_bits - 2
			end
		end
		-- now horizontal
		for y=1,size do
			number_of_consecutive_bits = 0
			last_bit_blank = nil
			for x = 1,size do
				is_blank = matrix[x][y] < 0
				if last_bit_blank == is_blank then
					number_of_consecutive_bits = number_of_consecutive_bits + 1
				else
					if number_of_consecutive_bits >= 5 then
						penalty1 = penalty1 + number_of_consecutive_bits - 2
					end
					number_of_consecutive_bits = 1
				end
				last_bit_blank = is_blank
			end
			if number_of_consecutive_bits >= 5 then
				penalty1 = penalty1 + number_of_consecutive_bits - 2
			end
		end
		for x=1,size do
			for y=1,size do
				-- 2: Block of modules in same color
				-- -----------------------------------
				-- Blocksize = m × n  -> 3 × (m-1) × (n-1)
				if (y < size - 1) and ( x < size - 1) and ( (matrix[x][y] < 0 and matrix[x+1][y] < 0 and matrix[x][y+1] < 0 and matrix[x+1][y+1] < 0) or (matrix[x][y] > 0 and matrix[x+1][y] > 0 and matrix[x][y+1] > 0 and matrix[x+1][y+1] > 0) ) then
					penalty2 = penalty2 + 3
				end

				-- 3: 1:1:3:1:1 ratio (dark:light:dark:light:dark) pattern in row/column
				-- ------------------------------------------------------------------
				-- Gives 40 points each
				--
				-- I have no idea why we need the extra 0000 on left or right side. The spec doesn't mention it,
				-- other sources do mention it. This is heavily inspired by zxing.
				if (y + 6 < size and
					matrix[x][y] > 0 and
					matrix[x][y +  1] < 0 and
					matrix[x][y +  2] > 0 and
					matrix[x][y +  3] > 0 and
					matrix[x][y +  4] > 0 and
					matrix[x][y +  5] < 0 and
					matrix[x][y +  6] > 0 and
					((y + 10 < size and
						matrix[x][y +  7] < 0 and
						matrix[x][y +  8] < 0 and
						matrix[x][y +  9] < 0 and
						matrix[x][y + 10] < 0) or
					(y - 4 >= 1 and
						matrix[x][y -  1] < 0 and
						matrix[x][y -  2] < 0 and
						matrix[x][y -  3] < 0 and
						matrix[x][y -  4] < 0))) then penalty3 = penalty3 + 40 end
				if (x + 6 <= size and
					matrix[x][y] > 0 and
					matrix[x +  1][y] < 0 and
					matrix[x +  2][y] > 0 and
					matrix[x +  3][y] > 0 and
					matrix[x +  4][y] > 0 and
					matrix[x +  5][y] < 0 and
					matrix[x +  6][y] > 0 and
					((x + 10 <= size and
						matrix[x +  7][y] < 0 and
						matrix[x +  8][y] < 0 and
						matrix[x +  9][y] < 0 and
						matrix[x + 10][y] < 0) or
					(x - 4 >= 1 and
						matrix[x -  1][y] < 0 and
						matrix[x -  2][y] < 0 and
						matrix[x -  3][y] < 0 and
						matrix[x -  4][y] < 0))) then penalty3 = penalty3 + 40 end
			end
		end
		-- 4: Proportion of dark modules in entire symbol
		-- ----------------------------------------------
		-- 50 ± (5 × k)% to 50 ± (5 × (k + 1))% -> 10 × k
		local dark_ratio = number_of_dark_cells / ( size * size )
		penalty4 = math.floor(math.abs(dark_ratio * 100 - 50)) * 2
		return penalty1 + penalty2 + penalty3 + penalty4
	end

	-- Create a matrix for the given parameters and calculate the penalty score.
	-- Return both (matrix and penalty)
	local function get_matrix_and_penalty(version,ec_level,data,mask)
		local tab = prepare_matrix_with_mask(version,ec_level,mask)
		add_data_to_matrix(tab,data,mask)
		local penalty = calculate_penalty(tab)
		return tab, penalty
	end

	-- Return the matrix with the smallest penalty. To to this
	-- we try out the matrix for all 8 masks and determine the
	-- penalty (score) each.
	local function get_matrix_with_lowest_penalty(version,ec_level,data)
		local tab, penalty
		local tab_min_penalty, min_penalty

		-- try masks 0-7
		tab_min_penalty, min_penalty = get_matrix_and_penalty(version,ec_level,data,0)
		for i=1,7 do
			tab, penalty = get_matrix_and_penalty(version,ec_level,data,i)
			if penalty < min_penalty then
				tab_min_penalty = tab
				min_penalty = penalty
			end
		end
		return tab_min_penalty
	end

	--- The main function. We connect everything together. Remember from above:
	---
	--- 1. Determine version, ec level and mode (=encoding) for codeword
	--- 1. Encode data
	--- 1. Arrange data and calculate error correction code
	--- 1. Generate 8 matrices with different masks and calculate the penalty
	--- 1. Return qrcode with least penalty
	-- If ec_level or mode is given, use the ones for generating the qrcode. (mode is not implemented yet)
	local function qrcode( str, ec_level, mode )
		local arranged_data, version, data_raw, mode, len_bitstring
		version, ec_level, data_raw, mode, len_bitstring = get_version_eclevel_mode_bistringlength(str,ec_level)
		data_raw = data_raw .. len_bitstring
		data_raw = data_raw .. encode_data(str,mode)
		data_raw = add_pad_data(version,ec_level,data_raw)
		arranged_data = arrange_codewords_and_calculate_ec(version,ec_level,data_raw)
		if math.fmod(#arranged_data,8) ~= 0 then
			return false, string.format("Arranged data %% 8 != 0: data length = %d, mod 8 = %d",#arranged_data, math.fmod(#arranged_data,8))
		end
		arranged_data = arranged_data .. string.rep("0",remainder[version])
		local tab = get_matrix_with_lowest_penalty(version,ec_level,arranged_data)
		return true, tab
	end


	_M.testing = function()
		return {
			encode_string_numeric = encode_string_numeric,
			encode_string_ascii = encode_string_ascii,
			qrcode = qrcode,
			binary = binary,
			get_mode = get_mode,
			get_length = get_length,
			add_pad_data = add_pad_data,
			get_generator_polynominal_adjusted = get_generator_polynominal_adjusted,
			get_pixel_with_mask = get_pixel_with_mask,
			get_version_eclevel_mode_bistringlength = get_version_eclevel_mode_bistringlength,
			remainder = remainder,
			--get_capacity_remainder = get_capacity_remainder,
			arrange_codewords_and_calculate_ec = arrange_codewords_and_calculate_ec,
			calculate_error_correction = calculate_error_correction,
			convert_bitstring_to_bytes = convert_bitstring_to_bytes,
			bit_xor = bit_xor,
		}
	end

	_M.test = function()
		function err( ... )
			print(string.format(...))
		end
		
		local failed = false
		function assert_equal( a,b,func )
			if a ~= b then
				err("Assertion failed: %s: %q is not equal to %q",func,tostring(a),tostring(b))
				failed = true
			end
		end
				
		local qrcode        = _M.testing()
		local tab
		str = "HELLO WORLD"
		assert_equal(qrcode.get_mode("0101"),           1,"get_encoding_byte 1")
		assert_equal(qrcode.get_mode(str),              2,"get_encoding_byte 2")
		assert_equal(qrcode.get_mode("0-9A-Z $%*./:+-"),2,"get_encoding_byte 3")
		assert_equal(qrcode.get_mode("foär"),           4,"get_encoding_byte 4")
		assert_equal(qrcode.get_length(str,1,2),"000001011","get_length")
		assert_equal(qrcode.binary(5,10),"0000000101","binary()")
		assert_equal(qrcode.binary(779,11),"01100001011","binary()")
		assert_equal(qrcode.add_pad_data(1,3,"0010101"),"00101010000000001110110000010001111011000001000111101100000100011110110000010001111011000001000111101100","pad_data")
		
		tab = qrcode.get_generator_polynominal_adjusted(13,25)
		assert_equal(tab[1],0,"get_generator_polynominal_adjusted 0")
		assert_equal(tab[24],74,"get_generator_polynominal_adjusted 24")
		assert_equal(tab[25],0,"get_generator_polynominal_adjusted 25")
		tab = qrcode.get_generator_polynominal_adjusted(13,24)
		assert_equal(tab[1],0,"get_generator_polynominal_adjusted 0")
		assert_equal(tab[23],74,"get_generator_polynominal_adjusted 23")
		assert_equal(tab[24],0,"get_generator_polynominal_adjusted 24")
		
		tab = qrcode.convert_bitstring_to_bytes("00100000010110110000101101111000110100010111001011011100010011010100001101000000111011000001000111101100")
		assert_equal(tab[1],32,"convert_bitstring_to_bytes")
		assert_equal(qrcode.bit_xor(141,43), 166,"bit_xor")
		assert_equal(qrcode.bit_xor(179,0), 179,"bit_xor")
		
		-- local hello_world_msg_with_ec = "0010000001011011000010110111100011010001011100101101110001001101010000110100000011101100000100011110110010101000010010000001011001010010110110010011011010011100000000000010111000001111101101000111101000010000"
		
		assert_equal(qrcode.get_pixel_with_mask(0,21,21,1),-1,"get_pixel_with_mask 1")
		assert_equal(qrcode.get_pixel_with_mask(0,1,1,1),-1,"get_pixel_with_mask 2")
		local a,b,c,d,e = qrcode.get_version_eclevel_mode_bistringlength(str)
		assert_equal(a,1,"get_version_eclevel_mode_bistringlength 1")
		assert_equal(b,3,"get_version_eclevel_mode_bistringlength 2")
		assert_equal(c,"0010","get_version_eclevel_mode_bistringlength 3")
		assert_equal(d,2,"get_version_eclevel_mode_bistringlength 4")
		assert_equal(e,"000001011","get_version_eclevel_mode_bistringlength 5")
		
		assert_equal(qrcode.encode_string_numeric("01234567"),"000000110001010110011000011","encode string numeric")
		assert_equal(qrcode.encode_string_ascii(str),"0110000101101111000110100010111001011011100010011010100001101","encode string ascii")
		assert_equal(qrcode.remainder[40],0,"get_remainder")
		assert_equal(qrcode.remainder[2],7,"get_remainder")
		
		
		-------------------
		-- Error correction
		-------------------
		local data = {32, 234, 187, 136, 103, 116, 252, 228, 127, 141, 73, 236, 12, 206, 138, 7, 230, 101, 30, 91, 152, 80, 0, 236, 17, 236, 17, 236}
		local ec_expected = {73, 31, 138, 44, 37, 176, 170, 36, 254, 246, 191, 187, 13, 137, 84, 63}
		local ec = qrcode.calculate_error_correction(data,16)
		for i=1,#ec_expected do
			assert_equal(ec_expected[i],ec[i],string.format("calculate_error_correction %d",i))
		end
		data = {32, 234, 187, 136, 103, 116, 252, 228, 127, 141, 73, 236, 12, 206, 138, 7, 230, 101, 30, 91, 152, 80, 0, 236, 17, 236, 17, 236, 17, 236, 17, 236, 17, 236}
		ec_expected = {66, 146, 126, 122, 79, 146, 2, 105, 180, 35}
		local ec = qrcode.calculate_error_correction(data,10)
		for i=1,#ec_expected do
			assert_equal(ec_expected[i],ec[i],string.format("calculate_error_correction %d",i))
		end
		data = {32, 83, 7, 120, 209, 114, 215, 60, 224}
		ec_expected = {123, 120, 222, 125, 116, 92, 144, 245, 58, 73, 104, 30, 108, 0, 30, 166, 152}
		local ec = qrcode.calculate_error_correction(data,17)
		for i=1,#ec_expected do
			assert_equal(ec_expected[i],ec[i],string.format("calculate_error_correction %d",i))
		end
		data = {32,83,7,120,209,114,215,60,224,236,17}
		ec_expected = {3, 67, 244, 57, 183, 14, 171, 101, 213, 52, 148, 3, 144, 148, 6, 155, 3, 252, 228, 100, 11, 56}
		local ec = qrcode.calculate_error_correction(data,22)
		for i=1,#ec_expected do
			assert_equal(ec_expected[i],ec[i],string.format("calculate_error_correction %d",i))
		end
		data = {236,17,236,17,236, 17,236, 17,236, 17,236}
		ec_expected = {171, 165, 230, 109, 241, 45, 198, 125, 213, 84, 88, 187, 89, 61, 220, 255, 150, 75, 113, 77, 147, 164}
		local ec = qrcode.calculate_error_correction(data,22)
		for i=1,#ec_expected do
			assert_equal(ec_expected[i],ec[i],string.format("calculate_error_correction %d",i))
		end
		data = {17,236, 17,236, 17,236,17,236, 17,236, 17,236}
		ec_expected = {23, 115, 68, 245, 125, 66, 203, 235, 85, 88, 174, 178, 229, 181, 118, 148, 44, 175, 213, 243, 27, 215}
		local ec = qrcode.calculate_error_correction(data,22)
		for i=1,#ec_expected do
			assert_equal(ec_expected[i],ec[i],string.format("calculate_error_correction %d",i))
		end
		
		-- "HALLO WELT" in alphanumeric, code 5-H
		data = { 32,83,7,120,209,114,215,60,224,236,17,236,17,236,17,236, 17,236, 17,236, 17,236, 17, 236, 17,236, 17,236, 17,236, 17,236, 17,236, 17, 236, 17,236, 17,236, 17,236, 17,236, 17,236}
		message_expected = {32, 236, 17, 17, 83, 17, 236, 236, 7, 236, 17, 17, 120, 17, 236, 236, 209, 236, 17, 17, 114, 17, 236, 236, 215, 236, 17, 17, 60, 17, 236, 236, 224, 236, 17, 17, 236, 17, 236, 236, 17, 236, 17, 17, 236, 236, 3, 171, 23, 23, 67, 165, 115, 115, 244, 230, 68, 68, 57, 109, 245, 245, 183, 241, 125, 125, 14, 45, 66, 66, 171, 198, 203, 203, 101, 125, 235, 235, 213, 213, 85, 85, 52, 84, 88, 88, 148, 88, 174, 174, 3, 187, 178, 178, 144, 89, 229, 229, 148, 61, 181, 181, 6, 220, 118, 118, 155, 255, 148, 148, 3, 150, 44, 44, 252, 75, 175, 175, 228, 113, 213, 213, 100, 77, 243, 243, 11, 147, 27, 27, 56, 164, 215, 215}
		tmp = qrcode.arrange_codewords_and_calculate_ec(5,4,data)
		message = qrcode.convert_bitstring_to_bytes(tmp)
		for i=1,#message do
			assert_equal(message_expected[i],message[i],string.format("arrange_codewords_and_calculate_ec %d",i))
		end
		
		--print("Tests end here")
		if failed then
			error("Some tests failed, see above")
		else --Fuxoft render tests
			local opts = assert(_M.opts)
			_M.init({character = "X", qr_doublewidth = true})
			local pkey = "L4DDkHFfLaRfRuHLf2xNcVyytugJ6bVkvrxxECDpTajDLJA4mDG7"
			assert(sha256(_M.render(pkey, 0)) == "d44e5cbaf7ee0e9ad1e34b48fd435a40f586ca4af18d59ef42f4f2992fae64f5", sha256(_M.render(pkey, 0)))
			_M.init({qr_invert=true, qr_halfheight=true})
			assert(sha256(_M.render(pkey, 3)) == "1562cc34d97e1cbb362ec86b65d75cc5658b5fefeefe033ba3f6637b426548a2", sha256(_M.render(pkey, 3)))
			_M.opts = opts --Restore the old options values
		end		
	end

	_M.qrcode = qrcode

	local function pad(tab, num)
		local function copy(lst)
			local cp = {}
			for i, num in ipairs(lst) do
				cp[i] = num
			end
			return cp
		end

		for rn, r in ipairs(tab) do
			table.insert(r, num)
			table.insert(r, 1, num)
		end
		local er = {}
		for i = 1, #tab[1] do
			table.insert(er, num)
		end
		table.insert(tab, copy(er))
		table.insert(tab, 1, copy(er))
		return tab
	end

	_M.init = function(o)
		_M.opts = {}
		opts = _M.opts

		if o.qr_invert then
			opts.invert = true
		end

		if o.qr_halfheight then
			opts.halfheight = true
			return
		end

		if o.qr_character then
			opts.character = o.qr_character
		else
			opts.character = "\226\150\136"
		end

		if o.qr_doublewidth then
			opts.doublewidth = true
		end
	end

	_M.render = function(data, leftmargin)
		local ok, ret = _M.qrcode(data)
		if not ok then
			error(result)
		end

		for i = 1, #ret do --Mirror it
			for j = 1, i do
				ret[i][j], ret[j][i] = ret[j][i], ret[i][j]
			end
		end

		ret = pad(ret, -2)
		ret = pad(ret, -2)
		ret = pad(ret, -2)
		ret = pad(ret, -2)

		if not leftmargin then
			leftmargin = 0
		end
		local margintxt = string.rep(" ", leftmargin)
		if _M.opts.halfheight then
			return _M.render_halfchars(ret, margintxt)
		end
		local empty, full = " ", assert(_M.opts.character)
		if _M.opts.invert then
			empty, full = full, empty
		end
		
		if _M.opts.doublewidth then
			empty = empty..empty
			full = full..full
		end

		local result = {}
		for rn, r in ipairs(ret) do
			local row = {margintxt}
			for i, num in ipairs(r) do
				if num > 0 then
					table.insert(row, full)
				else
					table.insert(row, empty)
				end
			end
			table.insert(result, table.concat(row))
		end
		return table.concat(result, "\n")
	end

	_M.render_halfchars = function(ret, margintxt)
		assert(margintxt)
		local upper = "▀"
		local lower = "▄"
		local full = "█"
		local empty = " "

		if _M.opts.invert then
			empty, full, upper, lower = full, empty, lower, upper
		end

		if #ret % 2 ~= 0 then
			table.insert(ret, ret[1])
		end
		local result = {}
		for rn = 1, #ret, 2 do
			local row = {margintxt}
			for i, num in ipairs(ret[rn]) do
				local chr = "?"
				if ret[rn+1][i] > 0 then
					if num > 0 then
						chr = full
					else
						chr = lower
					end
				else
					if num > 0 then
						chr = upper
					else
						chr = empty
					end
				end
				table.insert(row, assert(chr))
			end
			table.insert(result, table.concat(row))
		end
		return table.concat(result, "\n")
	end

	_M.init({})
	return _M
end

local function load_bignum()

	-- BigNum module
	local _M = {}
	local bpd = 30
	local maxd = bit.rol(1,bpd) - 1
	--print (bit.tohex(maxd))

	local function normalize(self)
		while #self > 1 and self[#self] == 0 do
			table.remove(self)
		end
		--print("normalized", table.concat(self, ","))
		return self
	end

	local mt = {}

	local function check_bignum(n)
		if not(getmetatable(n) == mt) then
			error (tostring(n).." is not a bignum")
		end
	end

	mt.__tostring = function(self, padding)
		--print(">", self[1], self.negative, "<")
		local cr = coroutine.create( function()
			for d = 1, #self do
				local digit, last = self[d], d==#self
				for b = 1, bpd do
					coroutine.yield (bit.band(digit, 1))
					digit = bit.rshift(digit, 1)
					if last and digit == 0 then
						while true do
							coroutine.yield(false)
						end
					end
				end
			end
		end)

		local result = {}
		local function get()
			local ok, got = coroutine.resume(cr)
			if not ok then
				error(got)
			end
			return got
		end
		while true do
			local d = get()
			if not d then
				break
			end
			d = d + 2 * (get() or 0) + 4 * (get() or 0) + 8 * (get() or 0)
			table.insert(result, 1, string.format("%x", d))
		end
		if not next(result) then
			result = {"0"}
		end
		if padding then
			while #result < padding do
				table.insert(result, 1, "0")
			end
		end
		table.insert(result, 1,"0x")
		if self.negative then
			table.insert(result, 1, "-")
		end
		return (table.concat(result))
	end

	mt.__eq = function(self, oth)
		check_bignum(oth)
		if self.negative ~= oth.negative then
			return false
		end
		if #self ~= #oth then
			return false 
		end
		for i, d in ipairs(self) do
			if d ~= oth[i] then
				return false
			end
		end
		return true
	end

	mt.__lt = function(self, oth)
		check_bignum(oth)
		if self.negative ~= oth.negative then
			return not oth.negative
		end
		if self == oth then
			return false
		end

		local function lt0(n1, n2) --assert not equal, ignore sign
			if #n1 ~= #n2 then
				return #n1 < #n2
			end
			for i = #n1, 1, -1 do
				if n1[i] ~= n2[i] then
					return n1[i] < n2[i]
				end
			end
			error("Shouldn't be equal")
		end

		if self.negative then
			return lt0(oth, self)
		else
			return lt0(self, oth)
		end
	end

	mt.__le = function(self, oth)
		check_bignum(oth)
		if self == oth then
			return true
		end
		return self < oth
	end

	_M.copy = function(self)
		check_bignum(self)
		local c = {}
		for k, v in pairs(self) do
			c[k] = v
		end
		setmetatable(c, mt)
		return c
	end

	_M.to_dwords = function(self, dw)
		self = _M.copy(self)
		local dwords = {}
		for i = 1, dw do
			local dword = bit.band(0xffff, self[1])
			_M.rshift(self, 16)
			dword = bit.bor(dword, bit.lshift(bit.band(0xffff, self[1]), 16))
			_M.rshift(self, 16)
			table.insert(dwords, 1, dword)
		end
		return dwords
	end

	mt.__unm = function(self)
		local x = _M.copy(self)
		if x ~= _M.zero then
			x.negative = not self.negative
		end
		--print("negated", self, x)
		return x
	end

	mt.__add = function(self, oth)
		--print("add", self, oth)

		check_bignum(oth)
		if oth == _M.zero then
			return self
		end
		
		if self == _M.zero then
			return oth
		end

		if self == -oth then
			return _M.zero
		end

		if self.negative ~= oth.negative then
			if oth.negative then
				return self - (-oth)
			else
				return - (-self - (oth))
			end
		end
		--Both have same sign
		if #self < #oth then
			self, oth = oth, self
		end
		local result = {negative = self.negative}
		setmetatable (result, mt)
		local carry = 0
		for i = 1, #self do
			local sum = self[i] + (oth[i] or 0) + carry
			result[i] = bit.band(maxd, sum)
			if sum > maxd then
				carry = 1
			else 
				carry = 0
			end
		end
		if carry == 1 then
			table.insert(result, 1)
		end
		return result
	end

	mt.__mul = function(self, oth)
		check_bignum(oth)
		
		local zero, one = _M.zero, _M.new(1)
		if self == one then
			return oth
		end

		if oth == one then
			return self
		end

		if self == zero or oth == zero then
			return zero
		end

		local acc = zero
		local m1, m2 = _M.abs(self), _M.abs(oth)
		if m1 < m2 then
			m1, m2 = m2, m1
		end
		--m1 >= m2
		m2 = _M.copy(m2) --Will be modified (shifted)
		while m2 ~= zero do
			if _M.rshift(m2, 1) ~= 0 then
				acc = acc + m1
			end
			m1 = m1 + m1
		end
		acc.negative = self.negative ~= oth.negative
		return acc
	end

	_M.pow = function(x, y, p) --a la Python
		local zero = _M.zero
		local acc = _M.new(1)
		local m1, m2 = _M.abs(x), _M.abs(y)
		m2 = _M.copy(m2) --Will be modified (shifted)
		assert(m2 > zero) -- ? TODO ?
		while m2 ~= zero do
			if _M.rshift(m2, 1) ~= 0 then
				acc = acc * m1
				if p then
					acc = _M.mod(acc, p)
				end
			end
			m1 = m1 * m1
			if p then
				m1 = _M.mod(m1, p)
			end
			--print(m1, acc, p)
		end
		return acc
	end

	mt.__sub = function(self, oth)
		--print("sub", self, oth)
		check_bignum(oth)
		if self == oth then
			return _M.zero
		end
		if oth == _M.zero then
			return self
		end
		if self == _M.zero then
			return -oth
		end

		if self.negative ~= oth.negative then
			if oth.negative then
				return self + (-oth)
			else
				return -(-self + oth)
			end
		end

		--assume same signs
		
		if self.negative then
			if self > oth then
				return (-oth - (-self))
			end
		else
			if self < oth then
				return -(oth - self)
			end
		end

		local result = {negative = self.negative}
		setmetatable(result, mt)

		local carry = 0

		for i = 1, #self do
			sum = self[i] - (oth[i] or 0) - carry
			if sum < 0 then
				sum = sum + maxd + 1
				carry = 1
			else
				carry = 0
			end
			result[i] = sum
		end
		assert(carry == 0)
		normalize(result)
		return(result)
	end

	_M.new = function(n)
		if type(n) == "number" then
			local int = n
			local num = {math.abs(int)}
			num.negative = int < 0
			setmetatable(num, mt)
			return num
		elseif type(n) == "string" then -- "0xffff"
			local num = _M.copy(_M.zero) --Needs copy because we modify it manually
			local digits = n:match("0x(.+)")
			for digit in digits:gmatch(".") do
				num = num + num
				num = num + num
				num = num + num
				num = num + num
				local d = tonumber(digit, 16)
				--print(d)
				assert(d, "Invalid char: "..digit)
				--print(num)
				num[1] = bit.bor(num[1], d)
				--print(num)
			end
			if n:match("^%-") then
				num.negative = true
			end
			return num
		else
			error("Invalid number type")
		end
	end

	_M.padding = function(num, chrs)
		return mt.__tostring(num, chrs)
	end

	_M.rshift = function(num, x) --Right shift x bits IN PLACE and return the overflown bits (already shifted!)
		check_bignum(num)
		assert(x < bpd)
		local mask = 2 ^ x - 1
		local carry = 0
		for i = #num, 1, -1 do
			local bits = bit.band(num[i], mask)
			num[i] = bit.bor(bit.rshift(num[i], x), carry)
			carry = bit.lshift(bits, bpd - x)
		end
		normalize(num)
		return carry
	end

	_M.divmod = function(x, y, fl) -- fl == true -> mod only
		fl = not fl
		local one = _M.new(1)
		if x.negative then
			if y.negative then -- -x, -y
				local d, m = _M.divmod0(-x, -y, fl)
				return d, -m
			else -- -x, +y
				local d, m = _M.divmod0(-x, y, fl)
				return -(d+one), y-m
			end
		else -- x > zero
			if y.negative then -- +x, -y
				local d, m = _M.divmod0(x, -y, fl)
				return -(d+one), y + m
			else -- +x, +y
				local d, m = _M.divmod0(x, y, fl)
				return d, m
			end
		end
	end

	_M.mod = function(x, y)
		local d, m = _M.divmod(x, y, true)
		--print("mod", d, m)
		return m
	end

	--[[divmod:
	100, 3 = 33, 1
	-100, -3 = 33, -1
	-100, 3 = -34, 2
	100, -3 = -34, -2
	]]

	_M.divmod0 = function(x, y, divmod)
		check_bignum(x)    
		check_bignum(y)
		--assume positive x, y
		assert(not x.negative)
		assert(not y.negative)
		local zero = _M.zero
		assert(x >= zero)
		assert(y > zero)
		local one = _M.new(1)
		if x < y then
			return zero, x
		end
		if y == one then
			return x, zero
		end
		assert(y > zero)

		local dm = zero

		local powers = {}
		local pow = y
		local ind = 0
		repeat
			ind = ind + 1
			powers[ind] = pow
			pow = pow + pow
		until pow > x
		for i = ind, 1, -1 do
			if divmod then
				dm = dm + dm
			end
			if powers[i] <= x then
				x = x - powers[i]
				if divmod then
					dm = dm + one
				end
			end
		end
		return dm, x
	end

	_M.zero = _M.new(0)

	_M.abs = function(num)
		if num >= _M.zero then
			return num
		end
		return -num
	end

	_M.test = function()
		assert(_M.new(-23) == _M.new(-23))
		assert(_M.new(-23) ~= _M.new(23))
		assert(_M.new(-23) == -_M.new(23))
		local sum = _M.zero
		math.randomseed(1)
		local iters = 20
		for i = 1, iters do
			local x = _M.new(math.random(maxd) - math.floor(maxd / 2))
			for i = 1, math.random(20) do
				x = x + x - _M.new(math.random(9))
			end
			if i <= iters / 2 then
			--    print("+", sum, x)
				sum = sum + x
			else
			--    print("-", sum, x)
				sum = sum - x
			end
			--print("sum is", sum)
			if i == iters / 2 then
				math.randomseed(1)
			end
		end
		assert(sum == _M.zero)
		assert(tostring(_M.new("-0x1234567890abcdef")) == "-0x1234567890abcdef")
		assert(_M.padding(_M.new("-0x12abc"),8) == "-0x00012abc")
		assert(_M.new("0x123456789") * _M.new("-0xdeadbeef") == _M.new("-0xFD5BDEED363856E7"))
		assert(_M.mod(_M.new("0x3b9ac9ff"), _M.new("0x3e7")) == _M.zero)
		assert(_M.mod(_M.new("0x1234567890"), _M.new("0x6789")) == _M.new("0x59a6"))
		for i, test in ipairs {{"0x64", "0x3", "0x21", "0x1"}, {"-0x64", "-0x3", "0x21", "-0x1"}, {"-0x64", "0x3", "-0x22", "0x2"}, {"0x64", "-0x3", "-0x22", "-0x2"}} do
			local x, y, d0, m0 = _M.new(test[1]), _M.new(test[2]), _M.new(test[3]), _M.new(test[4])
			local d, m = _M.divmod(x,y)
			--print(x, y, d0, m0)
			--print(d, m)
			assert(d == d0 and m == m0)
		end
		
		--assert(_M.pow(_M.new("0x10"), _M.new("0x3"), _M.new("0xbeef")) == _M.new("0x1000"))
		--assert(_M.pow(_M.new("0xabcdef"), _M.new("0x123456789"), _M.new("0x123456789abcdef")) == _M.new("0x2d357497e15f50"))
		--print(_M.pow(_M.new("0xabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdef"), _M.new("0x123456789123456789123456789123456789123456789123456789123456789123456789"), _M.new("0x123456789abcdef")))
	end

	return _M
end

local pubkey_cache = {}

local privkey_to_pubkey = function(secret0)
	assert(#secret0 > 30)
	if pubkey_cache[secret0] then
		print("Retrieved cached BTC pubkey.")
		return pubkey_cache[secret0]
	end
	local new = BIGNUM.new
	local zero = BIGNUM.zero
	local one = new(1)
	local two = new(2)
	local three = new(3)
	local p = new("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F")
	local g = {x=new("0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"), y=new("0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8")}
	local order = new("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141")
	local secret = new(secret0)

	local function inverse_mod(a)
		if a < zero or a >= p then
			a = BIGNUM.mod(a, p)
		end
		local c, d, uc, vc, ud, vd = a, p, one, zero, zero, one
		local q
		while c ~= zero do
			--print("call divmod", d, c)
			local c0 = c
			q, c = BIGNUM.divmod(d, c)
			d = c0
			--print("q c d", q, c, d)
			uc, vc, ud, vd = ud - q * uc, vd - q * vc, uc, vc
		end
		--print("while ended")
		--print("ud", ud)
		local bool = ud > zero 
		if ud > zero then
			return ud
		end
		return ud + p
	end

	local function calc(self, top, bottom, other_x)
		local l = BIGNUM.mod(top * inverse_mod(bottom), p)
		local x3 = BIGNUM.mod(l * l - self.x - other_x, p)
		return {x = x3, y = BIGNUM.mod(l * (self.x - x3) - self.y, p)}
	end

	local function double(self)
		if self == "inf" then
			return self
		end
		return calc(self, three * self.x * self.x, two * self.y, self.x)
	end

	local function add(self, other)
		if other == "inf" then
			return self
		end
		if self == "inf" then
			return other
		end
		if self.x == other.x then
			if BIGNUM.mod((self.y + other.y), p) == zero then
				return "inf"
			end
			return double(self)
		end
		return calc(self, other.y - self.y, other.x - self.x, other.x)
	end

	local function mult(self, e)
		e = BIGNUM.mod(e, order)
		e = BIGNUM.copy(e)
		local result, q = "inf", self
		local progress = 0
		io.write("Pubkey calculation (32 steps)")
		io.flush()
		while e ~= zero do
			if bit.band(e[1],1) == 1 then
				result = add(result, q)
			end
			BIGNUM.rshift(e, 1)
			q = double(q)
			--print("result", result.x, result.y)
			if progress % 8 == 0 then
				io.write(".")
				io.flush()
			end
			progress = progress + 1
		end
		print("done")
		return result
	end

	local pubkey0 = mult(g, secret)
	local pubkey = {x=BIGNUM.to_dwords(pubkey0.x,8), y=BIGNUM.to_dwords(pubkey0.y,8)}
	pubkey_cache[secret0] = pubkey
	return pubkey
end

local WORDLIST = {
	[0]="abandon", "ability", "able", "about", "above", "absent", "absorb", "abstract", "absurd", "abuse", "access", "accident", "account", "accuse", "achieve", "acid", "acoustic", "acquire", "across", "act", "action", "actor", "actress", "actual", "adapt", "add", "addict", "address", "adjust", "admit", "adult", "advance", "advice", "aerobic", "affair", "afford", "afraid", "again", "age", "agent", "agree", "ahead", "aim", "air", "airport", "aisle", "alarm", "album", "alcohol", "alert", "alien", "all", "alley", "allow", "almost", "alone", "alpha", "already", "also", "alter", "always", "amateur", "amazing", "among", "amount", "amused", "analyst", "anchor", "ancient", "anger", "angle", "angry", "animal", "ankle", "announce", "annual", "another", "answer", "antenna", "antique", "anxiety", "any", "apart", "apology", "appear", "apple", "approve", "april", "arch", "arctic", "area", "arena", "argue", "arm", "armed", "armor", "army", "around", "arrange", "arrest", "arrive", "arrow", "art", "artefact", "artist", "artwork", "ask", "aspect", "assault", "asset", "assist", "assume", "asthma", "athlete", "atom", "attack", "attend", "attitude", "attract", "auction", "audit", "august", "aunt", "author", "auto", "autumn", "average", "avocado", "avoid", "awake", "aware", "away", "awesome", "awful", "awkward", "axis", "baby", "bachelor", "bacon", "badge", "bag", "balance", "balcony", "ball", "bamboo", "banana", "banner", "bar", "barely", "bargain", "barrel", "base", "basic", "basket", "battle", "beach", "bean", "beauty", "because", "become", "beef", "before", "begin", "behave", "behind", "believe", "below", "belt", "bench", "benefit", "best", "betray", "better", "between", "beyond", "bicycle", "bid", "bike", "bind", "biology", "bird", "birth", "bitter", "black", "blade", "blame", "blanket", "blast", "bleak", "bless", "blind", "blood", "blossom", "blouse", "blue", "blur", "blush", "board", "boat", "body", "boil", "bomb", "bone", "bonus", "book", "boost", "border", "boring", "borrow", "boss", "bottom", "bounce", "box", "boy", "bracket", "brain", "brand", "brass", "brave", "bread", "breeze", "brick", "bridge", "brief", "bright", "bring", "brisk", "broccoli", "broken", "bronze", "broom", "brother", "brown", "brush", "bubble", "buddy", "budget", "buffalo", "build", "bulb", "bulk", "bullet", "bundle", "bunker", "burden", "burger", "burst", "bus", "business", "busy", "butter", "buyer", "buzz", "cabbage", "cabin", "cable", "cactus", "cage", "cake", "call", "calm", "camera", "camp", "can", "canal", "cancel", "candy", "cannon", "canoe", "canvas", "canyon", "capable", "capital", "captain", "car", "carbon", "card", "cargo", "carpet", "carry", "cart", "case", "cash", "casino", "castle", "casual", "cat", "catalog", "catch", "category", "cattle", "caught", "cause", "caution", "cave", "ceiling", "celery", "cement", "census", "century", "cereal", "certain", "chair", "chalk", "champion", "change", "chaos", "chapter", "charge", "chase", "chat", "cheap", "check", "cheese", "chef", "cherry", "chest", "chicken", "chief", "child", "chimney", "choice", "choose", "chronic", "chuckle", "chunk", "churn", "cigar", "cinnamon", "circle", "citizen", "city", "civil", "claim", "clap", "clarify", "claw", "clay", "clean", "clerk", "clever", "click", "client", "cliff", "climb", "clinic", "clip", "clock", "clog", "close", "cloth", "cloud", "clown", "club", "clump", "cluster", "clutch", "coach", "coast", "coconut", "code", "coffee", "coil", "coin", "collect", "color", "column", "combine", "come", "comfort", "comic", "common", "company", "concert", "conduct", "confirm", "congress", "connect", "consider", "control", "convince", "cook", "cool", "copper", "copy", "coral", "core", "corn", "correct", "cost", "cotton", "couch", "country", "couple", "course", "cousin", "cover", "coyote", "crack", "cradle", "craft", "cram", "crane", "crash", "crater", "crawl", "crazy", "cream", "credit", "creek", "crew", "cricket", "crime", "crisp", "critic", "crop", "cross", "crouch", "crowd", "crucial", "cruel", "cruise", "crumble", "crunch", "crush", "cry", "crystal", "cube", "culture", "cup", "cupboard", "curious", "current", "curtain", "curve", "cushion", "custom", "cute", "cycle", "dad", "damage", "damp", "dance", "danger", "daring", "dash", "daughter", "dawn", "day", "deal", "debate", "debris", "decade", "december", "decide", "decline", "decorate", "decrease", "deer", "defense", "define", "defy", "degree", "delay", "deliver", "demand", "demise", "denial", "dentist", "deny", "depart", "depend", "deposit", "depth", "deputy", "derive", "describe", "desert", "design", "desk", "despair", "destroy", "detail", "detect", "develop", "device", "devote", "diagram", "dial", "diamond", "diary", "dice", "diesel", "diet", "differ", "digital", "dignity", "dilemma", "dinner", "dinosaur", "direct", "dirt", "disagree", "discover", "disease", "dish", "dismiss", "disorder", "display", "distance", "divert", "divide", "divorce", "dizzy", "doctor", "document", "dog", "doll", "dolphin", "domain", "donate", "donkey", "donor", "door", "dose", "double", "dove", "draft", "dragon", "drama", "drastic", "draw", "dream", "dress", "drift", "drill", "drink", "drip", "drive", "drop", "drum", "dry", "duck", "dumb", "dune", "during", "dust", "dutch", "duty", "dwarf", "dynamic", "eager", "eagle", "early", "earn", "earth", "easily", "east", "easy", "echo", "ecology", "economy", "edge", "edit", "educate", "effort", "egg", "eight", "either", "elbow", "elder", "electric", "elegant", "element", "elephant", "elevator", "elite", "else", "embark", "embody", "embrace", "emerge", "emotion", "employ", "empower", "empty", "enable", "enact", "end", "endless", "endorse", "enemy", "energy", "enforce", "engage", "engine", "enhance", "enjoy", "enlist", "enough", "enrich", "enroll", "ensure", "enter", "entire", "entry", "envelope", "episode", "equal", "equip", "era", "erase", "erode", "erosion", "error", "erupt", "escape", "essay", "essence", "estate", "eternal", "ethics", "evidence", "evil", "evoke", "evolve", "exact", "example", "excess", "exchange", "excite", "exclude", "excuse", "execute", "exercise", "exhaust", "exhibit", "exile", "exist", "exit", "exotic", "expand", "expect", "expire", "explain", "expose", "express", "extend", "extra", "eye", "eyebrow", "fabric", "face", "faculty", "fade", "faint", "faith", "fall", "false", "fame", "family", "famous", "fan", "fancy", "fantasy", "farm", "fashion", "fat", "fatal", "father", "fatigue", "fault", "favorite", "feature", "february", "federal", "fee", "feed", "feel", "female", "fence", "festival", "fetch", "fever", "few", "fiber", "fiction", "field", "figure", "file", "film", "filter", "final", "find", "fine", "finger", "finish", "fire", "firm", "first", "fiscal", "fish", "fit", "fitness", "fix", "flag", "flame", "flash", "flat", "flavor", "flee", "flight", "flip", "float", "flock", "floor", "flower", "fluid", "flush", "fly", "foam", "focus", "fog", "foil", "fold", "follow", "food", "foot", "force", "forest", "forget", "fork", "fortune", "forum", "forward", "fossil", "foster", "found", "fox", "fragile", "frame", "frequent", "fresh", "friend", "fringe", "frog", "front", "frost", "frown", "frozen", "fruit", "fuel", "fun", "funny", "furnace", "fury", "future", "gadget", "gain", "galaxy", "gallery", "game", "gap", "garage", "garbage", "garden", "garlic", "garment", "gas", "gasp", "gate", "gather", "gauge", "gaze", "general", "genius", "genre", "gentle", "genuine", "gesture", "ghost", "giant", "gift", "giggle", "ginger", "giraffe", "girl", "give", "glad", "glance", "glare", "glass", "glide", "glimpse", "globe", "gloom", "glory", "glove", "glow", "glue", "goat", "goddess", "gold", "good", "goose", "gorilla", "gospel", "gossip", "govern", "gown", "grab", "grace", "grain", "grant", "grape", "grass", "gravity", "great", "green", "grid", "grief", "grit", "grocery", "group", "grow", "grunt", "guard", "guess", "guide", "guilt", "guitar", "gun", "gym", "habit", "hair", "half", "hammer", "hamster", "hand", "happy", "harbor", "hard", "harsh", "harvest", "hat", "have", "hawk", "hazard", "head", "health", "heart", "heavy", "hedgehog", "height", "hello", "helmet", "help", "hen", "hero", "hidden", "high", "hill", "hint", "hip", "hire", "history", "hobby", "hockey", "hold", "hole", "holiday", "hollow", "home", "honey", "hood", "hope", "horn", "horror", "horse", "hospital", "host", "hotel", "hour", "hover", "hub", "huge", "human", "humble", "humor", "hundred", "hungry", "hunt", "hurdle", "hurry", "hurt", "husband", "hybrid", "ice", "icon", "idea", "identify", "idle", "ignore", "ill", "illegal", "illness", "image", "imitate", "immense", "immune", "impact", "impose", "improve", "impulse", "inch", "include", "income", "increase", "index", "indicate", "indoor", "industry", "infant", "inflict", "inform", "inhale", "inherit", "initial", "inject", "injury", "inmate", "inner", "innocent", "input", "inquiry", "insane", "insect", "inside", "inspire", "install", "intact", "interest", "into", "invest", "invite", "involve", "iron", "island", "isolate", "issue", "item", "ivory", "jacket", "jaguar", "jar", "jazz", "jealous", "jeans", "jelly", "jewel", "job", "join", "joke", "journey", "joy", "judge", "juice", "jump", "jungle", "junior", "junk", "just", "kangaroo", "keen", "keep", "ketchup", "key", "kick", "kid", "kidney", "kind", "kingdom", "kiss", "kit", "kitchen", "kite", "kitten", "kiwi", "knee", "knife", "knock", "know", "lab", "label", "labor", "ladder", "lady", "lake", "lamp", "language", "laptop", "large", "later", "latin", "laugh", "laundry", "lava", "law", "lawn", "lawsuit", "layer", "lazy", "leader", "leaf", "learn", "leave", "lecture", "left", "leg", "legal", "legend", "leisure", "lemon", "lend", "length", "lens", "leopard", "lesson", "letter", "level", "liar", "liberty", "library", "license", "life", "lift", "light", "like", "limb", "limit", "link", "lion", "liquid", "list", "little", "live", "lizard", "load", "loan", "lobster", "local", "lock", "logic", "lonely", "long", "loop", "lottery", "loud", "lounge", "love", "loyal", "lucky", "luggage", "lumber", "lunar", "lunch", "luxury", "lyrics", "machine", "mad", "magic", "magnet", "maid", "mail", "main", "major", "make", "mammal", "man", "manage", "mandate", "mango", "mansion", "manual", "maple", "marble", "march", "margin", "marine", "market", "marriage", "mask", "mass", "master", "match", "material", "math", "matrix", "matter", "maximum", "maze", "meadow", "mean", "measure", "meat", "mechanic", "medal", "media", "melody", "melt", "member", "memory", "mention", "menu", "mercy", "merge", "merit", "merry", "mesh", "message", "metal", "method", "middle", "midnight", "milk", "million", "mimic", "mind", "minimum", "minor", "minute", "miracle", "mirror", "misery", "miss", "mistake", "mix", "mixed", "mixture", "mobile", "model", "modify", "mom", "moment", "monitor", "monkey", "monster", "month", "moon", "moral", "more", "morning", "mosquito", "mother", "motion", "motor", "mountain", "mouse", "move", "movie", "much", "muffin", "mule", "multiply", "muscle", "museum", "mushroom", "music", "must", "mutual", "myself", "mystery", "myth", "naive", "name", "napkin", "narrow", "nasty", "nation", "nature", "near", "neck", "need", "negative", "neglect", "neither", "nephew", "nerve", "nest", "net", "network", "neutral", "never", "news", "next", "nice", "night", "noble", "noise", "nominee", "noodle", "normal", "north", "nose", "notable", "note", "nothing", "notice", "novel", "now", "nuclear", "number", "nurse", "nut", "oak", "obey", "object", "oblige", "obscure", "observe", "obtain", "obvious", "occur", "ocean", "october", "odor", "off", "offer", "office", "often", "oil", "okay", "old", "olive", "olympic", "omit", "once", "one", "onion", "online", "only", "open", "opera", "opinion", "oppose", "option", "orange", "orbit", "orchard", "order", "ordinary", "organ", "orient", "original", "orphan", "ostrich", "other", "outdoor", "outer", "output", "outside", "oval", "oven", "over", "own", "owner", "oxygen", "oyster", "ozone", "pact", "paddle", "page", "pair", "palace", "palm", "panda", "panel", "panic", "panther", "paper", "parade", "parent", "park", "parrot", "party", "pass", "patch", "path", "patient", "patrol", "pattern", "pause", "pave", "payment", "peace", "peanut", "pear", "peasant", "pelican", "pen", "penalty", "pencil", "people", "pepper", "perfect", "permit", "person", "pet", "phone", "photo", "phrase", "physical", "piano", "picnic", "picture", "piece", "pig", "pigeon", "pill", "pilot", "pink", "pioneer", "pipe", "pistol", "pitch", "pizza", "place", "planet", "plastic", "plate", "play", "please", "pledge", "pluck", "plug", "plunge", "poem", "poet", "point", "polar", "pole", "police", "pond", "pony", "pool", "popular", "portion", "position", "possible", "post", "potato", "pottery", "poverty", "powder", "power", "practice", "praise", "predict", "prefer", "prepare", "present", "pretty", "prevent", "price", "pride", "primary", "print", "priority", "prison", "private", "prize", "problem", "process", "produce", "profit", "program", "project", "promote", "proof", "property", "prosper", "protect", "proud", "provide", "public", "pudding", "pull", "pulp", "pulse", "pumpkin", "punch", "pupil", "puppy", "purchase", "purity", "purpose", "purse", "push", "put", "puzzle", "pyramid", "quality", "quantum", "quarter", "question", "quick", "quit", "quiz", "quote", "rabbit", "raccoon", "race", "rack", "radar", "radio", "rail", "rain", "raise", "rally", "ramp", "ranch", "random", "range", "rapid", "rare", "rate", "rather", "raven", "raw", "razor", "ready", "real", "reason", "rebel", "rebuild", "recall", "receive", "recipe", "record", "recycle", "reduce", "reflect", "reform", "refuse", "region", "regret", "regular", "reject", "relax", "release", "relief", "rely", "remain", "remember", "remind", "remove", "render", "renew", "rent", "reopen", "repair", "repeat", "replace", "report", "require", "rescue", "resemble", "resist", "resource", "response", "result", "retire", "retreat", "return", "reunion", "reveal", "review", "reward", "rhythm", "rib", "ribbon", "rice", "rich", "ride", "ridge", "rifle", "right", "rigid", "ring", "riot", "ripple", "risk", "ritual", "rival", "river", "road", "roast", "robot", "robust", "rocket", "romance", "roof", "rookie", "room", "rose", "rotate", "rough", "round", "route", "royal", "rubber", "rude", "rug", "rule", "run", "runway", "rural", "sad", "saddle", "sadness", "safe", "sail", "salad", "salmon", "salon", "salt", "salute", "same", "sample", "sand", "satisfy", "satoshi", "sauce", "sausage", "save", "say", "scale", "scan", "scare", "scatter", "scene", "scheme", "school", "science", "scissors", "scorpion", "scout", "scrap", "screen", "script", "scrub", "sea", "search", "season", "seat", "second", "secret", "section", "security", "seed", "seek", "segment", "select", "sell", "seminar", "senior", "sense", "sentence", "series", "service", "session", "settle", "setup", "seven", "shadow", "shaft", "shallow", "share", "shed", "shell", "sheriff", "shield", "shift", "shine", "ship", "shiver", "shock", "shoe", "shoot", "shop", "short", "shoulder", "shove", "shrimp", "shrug", "shuffle", "shy", "sibling", "sick", "side", "siege", "sight", "sign", "silent", "silk", "silly", "silver", "similar", "simple", "since", "sing", "siren", "sister", "situate", "six", "size", "skate", "sketch", "ski", "skill", "skin", "skirt", "skull", "slab", "slam", "sleep", "slender", "slice", "slide", "slight", "slim", "slogan", "slot", "slow", "slush", "small", "smart", "smile", "smoke", "smooth", "snack", "snake", "snap", "sniff", "snow", "soap", "soccer", "social", "sock", "soda", "soft", "solar", "soldier", "solid", "solution", "solve", "someone", "song", "soon", "sorry", "sort", "soul", "sound", "soup", "source", "south", "space", "spare", "spatial", "spawn", "speak", "special", "speed", "spell", "spend", "sphere", "spice", "spider", "spike", "spin", "spirit", "split", "spoil", "sponsor", "spoon", "sport", "spot", "spray", "spread", "spring", "spy", "square", "squeeze", "squirrel", "stable", "stadium", "staff", "stage", "stairs", "stamp", "stand", "start", "state", "stay", "steak", "steel", "stem", "step", "stereo", "stick", "still", "sting", "stock", "stomach", "stone", "stool", "story", "stove", "strategy", "street", "strike", "strong", "struggle", "student", "stuff", "stumble", "style", "subject", "submit", "subway", "success", "such", "sudden", "suffer", "sugar", "suggest", "suit", "summer", "sun", "sunny", "sunset", "super", "supply", "supreme", "sure", "surface", "surge", "surprise", "surround", "survey", "suspect", "sustain", "swallow", "swamp", "swap", "swarm", "swear", "sweet", "swift", "swim", "swing", "switch", "sword", "symbol", "symptom", "syrup", "system", "table", "tackle", "tag", "tail", "talent", "talk", "tank", "tape", "target", "task", "taste", "tattoo", "taxi", "teach", "team", "tell", "ten", "tenant", "tennis", "tent", "term", "test", "text", "thank", "that", "theme", "then", "theory", "there", "they", "thing", "this", "thought", "three", "thrive", "throw", "thumb", "thunder", "ticket", "tide", "tiger", "tilt", "timber", "time", "tiny", "tip", "tired", "tissue", "title", "toast", "tobacco", "today", "toddler", "toe", "together", "toilet", "token", "tomato", "tomorrow", "tone", "tongue", "tonight", "tool", "tooth", "top", "topic", "topple", "torch", "tornado", "tortoise", "toss", "total", "tourist", "toward", "tower", "town", "toy", "track", "trade", "traffic", "tragic", "train", "transfer", "trap", "trash", "travel", "tray", "treat", "tree", "trend", "trial", "tribe", "trick", "trigger", "trim", "trip", "trophy", "trouble", "truck", "true", "truly", "trumpet", "trust", "truth", "try", "tube", "tuition", "tumble", "tuna", "tunnel", "turkey", "turn", "turtle", "twelve", "twenty", "twice", "twin", "twist", "two", "type", "typical", "ugly", "umbrella", "unable", "unaware", "uncle", "uncover", "under", "undo", "unfair", "unfold", "unhappy", "uniform", "unique", "unit", "universe", "unknown", "unlock", "until", "unusual", "unveil", "update", "upgrade", "uphold", "upon", "upper", "upset", "urban", "urge", "usage", "use", "used", "useful", "useless", "usual", "utility", "vacant", "vacuum", "vague", "valid", "valley", "valve", "van", "vanish", "vapor", "various", "vast", "vault", "vehicle", "velvet", "vendor", "venture", "venue", "verb", "verify", "version", "very", "vessel", "veteran", "viable", "vibrant", "vicious", "victory", "video", "view", "village", "vintage", "violin", "virtual", "virus", "visa", "visit", "visual", "vital", "vivid", "vocal", "voice", "void", "volcano", "volume", "vote", "voyage", "wage", "wagon", "wait", "walk", "wall", "walnut", "want", "warfare", "warm", "warrior", "wash", "wasp", "waste", "water", "wave", "way", "wealth", "weapon", "wear", "weasel", "weather", "web", "wedding", "weekend", "weird", "welcome", "west", "wet", "whale", "what", "wheat", "wheel", "when", "where", "whip", "whisper", "wide", "width", "wife", "wild", "will", "win", "window", "wine", "wing", "wink", "winner", "winter", "wire", "wisdom", "wise", "wish", "witness", "wolf", "woman", "wonder", "wood", "wool", "word", "work", "world", "worry", "worth", "wrap", "wreck", "wrestle", "wrist", "write", "wrong", "yard", "year", "yellow", "you", "young", "youth", "zebra", "zero", "zone", "zoo"
}

local function bin_to_any_module()
	--convert binary stream to any base
	local _M = {}
	local bit = require("bit")

	_M.powers2 = {}
	_M.alphabets = {}

	local function powers2(exp, base)
		assert(exp >= 0)
		if not _M.powers2[base] then
			_M.powers2[base] = {[0] = {1}}
		end
		local cache = assert(_M.powers2[base])
		if cache[exp] then
			return cache[exp]
		end
		local prev = powers2(exp - 1, base)
		local mult = {}
		local carry = 0
		local nums = #prev
		for i = 1, nums do
			local m = prev[i] * 2 + carry
			if m < base then
				mult[i] = m
				carry = 0
			else
				mult[i] = m - base
				carry = 1
			end
		end
		if carry == 1 then
			mult[nums + 1] = 1
		end
		cache[exp] = mult
		return mult
	end

	local function display(num, alphabet0, pad)
		--print("pad", pad)
		local digits = #num
		local alph = _M.alphabets[alphabet0]
		if not alph then
			alph = {}
			assert(#alphabet0 >= 2)
			for i = 1, #alphabet0 do
				alph[i-1] = alphabet0:sub(i,i)
			end
			_M.alphabets[alphabet0] = alph
		end
		local res = {}
		if pad and (digits < pad) then
			for i = 1, pad - digits do
				res[i] = assert(alph[0])
			end
		end

		for i = digits, 1, -1 do
			table.insert(res,assert(alph[num[i]]))
		end
		return table.concat(res)
	end

	function _M.convert(generator_or_chars, base_or_alphabet, maybe_pad)
		local base, alphabet
		if type(base_or_alphabet) == "number" then
			base = base_or_alphabet
			assert(base > 2)
		else
			base = #base_or_alphabet
			alphabet = base_or_alphabet
		end
		local generator = generator_or_chars
		if type(generator) == "string" then
			local str = generator_or_chars
			generator = coroutine.wrap(function()
				for ind = #str, 1, -1 do
					local byte = string.byte(str:sub(ind))
					--print("byte", string.format("%02x", byte))
					for bitn = 1, 8 do
						coroutine.yield(bit.band(byte,1))
						byte = bit.rshift(byte,1)
					end
				end
			end)
		end
		local acc = {0}
		local exp = 0
		while true do
			local next = generator()
			if not next then
				break
			end
			if next == 1 then --add it
				local pow = powers2(exp, base)
				local digits = #pow
				local carry = 0
				for i = 1, digits do
					local a = (acc[i] or 0) + pow[i] + carry
					if a < base then
						acc[i] = a
						carry = 0
					else
						acc[i] = a - base
						carry = 1
					end
				end
				if carry == 1 then
					acc[digits + 1] = 1
				end
			end
			exp = exp + 1
		end
		if not alphabet then
			return acc
		else
			return display(acc, alphabet, maybe_pad), acc
		end
	end

	return _M
end

local function dwords_to_chars(ns)
	local res = {}
	for ndw, dword in ipairs(ns) do
		for i = 1,4 do
			dword = rol(dword,8)
			table.insert(res, string.char(band(0xff, dword)))
		end
	end
	return table.concat(res)
end

local function chars_to_dwords(str)
	while #str == 0 or (#str % 4 ~= 0) do
		str = string.char(0)..str
	end
	local result = {}
	for idwrd = 1, #str, 4 do
		local dword = 0
		for j = 0, 3 do
			dword = bor(rol(dword,8), string.byte(str:sub(idwrd + j)))
		end
		table.insert(result, dword)
	end
	return result
end

local function dwords_to_password(dwords,fives)
	fives = fives or 8
	local chars = "$*23456789abcdef@hijk(mnop)rstuvwxyzABCDEFGH=JKLMN#PQRSTUVWXYZ!?"
	assert(#dwords == 8)
	local result = {}
	for i = 1, fives do
		local dword = assert(dwords[i])
		for j = 1, 5 do
			dword = rol(dword,6)
			local num = band(dword, 63) + 1
			table.insert(result,string.sub(chars,num,num))
		end
	end
	return table.concat(result)
end

local function get256bits(rand)
	local dwords = {}
	for i = 1, 8 do
		local dword = 0
		for j = 1, 32 do
			local got = rand()
			local bitsel = band(got, 0xf) --bit 0-15
			dword = rol(dword,1)
			dword = bor(dword, band(1,ror(got, bitsel + 8)))
		end
		dwords[i] = dword
	end
	return dwords
end

local function to_base58(dwords_or_chars)
	if type(dwords_or_chars) == "table" then
		dwords_or_chars = dwords_to_chars(dwords_or_chars)
	end
	return (BIN_TO_ANY.convert(dwords_or_chars,"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"))
end

local function to_bin(dwords)
	if type(dwords) == "number" then
		dwords = {dwords}
	end
	local res = {}
	for dwi, dword in ipairs(dwords) do
		for i = 1,32 do
			dword = rol(dword,1)
			table.insert(res, band(dword, 1))
		end
	end
	assert(#res == 32 * #dwords)
	return (res)
end

local function to_binstr(n)
	return table.concat(to_bin(n))
end

local bitstream = function(rem_bits)
	return (function (take)
		assert(take <= 32)
		local result = 0
		for i = 1, take do
			result = rol(result, 1)
			result = bor(result, table.remove(rem_bits, 1))
		end
		return result
	end)
end

local function ripemd160(input, format)
	local function swap_endian(dw)
		local n = 0
		for j = 1, 4 do
			n = bor(lshift(n, 8), band(0xff, dw))
			dw = rshift(dw, 8)
		end
		return n
	end
	local len = #input
	input = input .. "\128"
	while #input % 64 ~= 56 do
		input = input .. "\000"
	end
	input = input .. dwords_to_chars({swap_endian(len * 8)})
	input = input .. "\000\000\000\000" --LOL, not likely to exceed 32bit length
	assert(#input % 64 == 0)
	
	local funs = {}
	local funs = {
		[0] = function(x, y, z) return bxor(x, y, z) end,
		function(x, y, z) return bor(band(x, y), band(bnot(x), z)) end,
		function(x, y, z) return bxor(bor(x, bnot(y)), z) end,
		function(x, y, z) return bor(band(x, z), band(y, bnot(z))) end,
		function(x, y, z) return bxor(x, bor(y, bnot(z))) end
	}

	local K = {[0] = 0, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E}
	local K2 = {[0] = 0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0}
	local r = {
		[0] = 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    	7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
    	3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
    	1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
		4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13
	}
	local r2 = {
    	[0] = 5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
    	6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
    	15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
    	8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
		12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11
	}
	local s = {
		[0] = 11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
    	7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
    	11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
    	11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
		9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6
	}
	local s2 = {
		[0] = 8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
    	9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
    	9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
    	15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
		8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11
	}
	local function f(j, x, y, z)
		local res = funs[rshift(j,4)](x, y, z)
		--print("f result", tohex(res))
		return res
	end
	local h0, h1, h2, h3, h4 = 0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0	
	for blk in input:gmatch("(................................................................)") do
		local A, B, C, D, E = h0, h1, h2, h3, h4
		local A2, B2, C2, D2, E2 = h0, h1, h2, h3, h4
		local X = {}
		for i = 0, 63 do
			local ind = rshift(i, 2)
			X[ind] = ror(bor(X[ind] or 0, string.byte(blk:sub(i+1))), 8)
		end
		
		for j = 0, 79 do
			local jsh = rshift(j, 4)
			--print("A f X K s E", tohex(A), tohex(f(j,B,C,D)), tohex (X[r[j]]), tohex(K[jsh]), s[j], tohex(E))
			local T = tobit(rol (tobit(A + f(j, B, C, D) + X[r[j]] + K[jsh]), s[j]) + E)
			--print("T1", tohex(T))
			A = E; E = D; D = rol(C, 10); C = B; B = T
			T = tobit(rol(tobit(A2 + f(79-j, B2, C2, D2) + X[r2[j]] + K2[jsh]), s2[j]) + E2)
			A2 = E2; E2 = D2; D2 = rol(C2, 10); C2 = B2; B2 = T
		end
		local T = bit.tobit(h1 + C + D2)
		h1 = bit.tobit(h2 + D + E2)
		h2 = bit.tobit(h3 + E + A2)
		h3 = bit.tobit(h4 + A + B2)
		h4 = bit.tobit(h0 + B + C2)
		h0 = T
		--print ("h0-4:",tohex(h0), tohex(h1), tohex(h2), tohex(h3), tohex(h4))
	end
	local result = {h0, h1, h2, h3, h4}
	for i = 1, 5 do
		result[i] = swap_endian(result[i])
	end
	if format == "dwords" then
		return result
	end
	for i = 1, 5 do
		result[i] = bit.tohex(result[i])
	end
	--print(table.concat(result))
	return table.concat(result)
end

local new_shifter = function(state)
	if tobit(state) == 0 then
		state = 1
	end
	local fun = function(arg)
		if arg=="dump" then
			return (state)
		end
		local bt = band(state,1)
		state = rshift(state,1)
		if bt == 1 then
			state = bxor(state, 0xa3000000)
			return true
		end
		return false
	end
	return fun
	-- A3000000 = 1010 0011 0000 0000 0000 0000 0000 0000 - bits 32,30,26,25
end

local new_random = function(dwords) ---Not txt...
	local w,x,y,z = dwords[1],dwords[2],dwords[3],dwords[4]
	local sh1, sh2, sh3, sh4 = new_shifter(dwords[5]), new_shifter(dwords[6]), new_shifter(dwords[7]), new_shifter(dwords[8])

	if bit.bor(w,x,y,z) == 0 then --Cannot be all zeroes!
		w,x,y,z = 0,0,0,1
	end
	local fun = function(arg) --Xorshift algorithm
		if arg=="dump" then
			return{w,x,y,z, sh1("dump"), sh2("dump"), sh3("dump"), sh4("dump")}
		end
		repeat
			local t = bxor(x, lshift(x,11))
			x,y,z = y,z,w
			w = bit.bxor(w, rshift(w,19), t, rshift(t,8))
		until sh1() or sh2() or sh3() or sh4() --Shifters depend on each other
		return w
	end
	for i = 1, 10 do
		fun()
	end
	return fun
end

local function bip39(dwords)
	assert(#dwords >= 1 and #dwords <= 8)
	local chars = dwords_to_chars(dwords)
	local sha = to_bin(sha256(chars, "dwords"))
	local result = to_bin(dwords)
	local chksum = bitstream(sha)
	for i = 1, #dwords do
		table.insert(result, chksum(1))
	end
	assert(#result == #dwords * 33)
	local resultstr = {}
	local bs = bitstream(result)
	for i = 1, #dwords * 3 do
		table.insert(resultstr, assert(WORDLIST[bs(11)]))
	end
	return table.concat(resultstr, " ")
end

local function keymaster(seedstring, difc, progress)
	local prgfnc = function() end
	local iterations = 0x100000
	local one64 = rshift(iterations, 6)
	if progress then
		local prg = "012345abcdefghijklmnopqrstuvwxyz012345ABCDEFGHIJKLMNOPQRSTUVWXYZ"
		local progressbar = {}
		for i = 1, 64 do
			progressbar[i] = prg:sub(i,i)
		end
		io.write("Progress: ")
		local count = 1
		prgfnc = function()
			io.write(string.format(progressbar[count]))
			io.flush()
			if count == 64 then
				print()
			end
			count = count + 1
		end
	end

	local rnd = new_random(sha256(seedstring, "dwords"))
	local difmask = bit.rshift(0xffffffff, 32-difc)
	local t0 = os.time()
	for round = 1, 64 do
		prgfnc()
		for i = 1, one64 do
			difmask = ror(difmask, band(rnd(), 31))
			local seek = band(difmask, rnd())
--			print("looking for "..tohex(seek)..", mask: "..tohex(difmask))
			repeat
				local got = band(difmask,rnd())
			until got == seek
		end
	end
	local master = get256bits(rnd)
	return master, os.time()-t0
end

local function calibrate()
	for difc = 1, MAXDIFC do
		print("Trying difficulty "..difc)
		local gotrnd, time = keymaster("Xuul",difc,true)
		print("Seconds: "..time)
		print()
		if time >= 10 then
			print("\nCALIBRATION RESULTS FOR THIS MACHINE:")
			for d = difc, MAXDIFC do
				local t = time
				local ts = t.." seconds"
				if t > 180 then
					t = math.floor(t/60)
					ts = t.. " minutes"
					if t > 180 then
						t = math.floor(t / 60)
						ts = t.." hours"
						if t > 72 then
							t = math.floor( t / 24)
							ts = t.." days"
							if t > 1000 then
								t = math.floor(t / 365)
								ts = t.." years"
							end
						end
					end
				end
				print("Difficulty "..d.." takes approx. "..ts..".")

				time = time * 2
			end
			return
		end
	end
end

local function base58check(str)
	local chk = (sha256(str, "dwords"))
	chk = sha256(dwords_to_chars(chk),"dwords")[1]
	for i = 1, 4 do
		chk = rol(chk, 8)
		str = str .. string.char(band(chk, 0xff))
	end
	--print(#str)
	local zeroes = 0
	for i=1, #str do
		if str:sub(i,i) == "\000" then
			zeroes = zeroes + 1
		else
			break
		end
	end
	return string.rep("1",zeroes)..to_base58(str)
end

local function btc_privkey(dwords)
	if (dwords[1] == 0 or dwords[1] == 0xffffffff) and (dwords[1] == dwords[2]) and (dwords[2] == dwords[3]) then
		print("?!?!?!?!?! First 3 dwords are the same !?!?!?!?!?!?! BTC key very suspicious") --Hmm, LOL
	end
	local result = {}
	for ii, typ in ipairs{"compressed", "uncompressed"} do
		local str = string.char(0x80)..dwords_to_chars(dwords)
		if typ == "compressed" then
			str = str .. string.char(0x01)
		end
		result[typ] = base58check(str)
	end
	return result
end

local function wif(dwpubkey, comp)
	local str
	if comp ~= "compressed" then
		str = "\004"..dwords_to_chars(dwpubkey.x)..dwords_to_chars(dwpubkey.y)
		assert(#str == 65)
	else --compressed
		str = dwords_to_chars(dwpubkey.x)
		if bit.band(dwpubkey.y[8],1) == 0 then
			str = "\002" .. str
		else
			str = "\003" .. str
		end
		assert(#str == 33)
	end
	local step2 = sha256(str, "dwords")
	local step3 = ripemd160(dwords_to_chars(step2), "dwords")
	local step4 = "\000"..dwords_to_chars(step3)
	return(base58check(step4))
end

local function checkwords(str, howmany)
	if not howmany then
		howmany = 2
	end
	assert(howmany >= 1 and howmany <=8)
	local ichksum = sha256(str.."\000checkwords", "dwords")
	local result = {}
	for i = 1, howmany do
		result[i] = assert(WORDLIST[band(ichksum[i], 0x7ff)])
	end
	return table.concat(result, " ")
end

local function get_all_prefixes()
	return {hex = true, btcc = true, btcu = true, pwd15 = true, pwd40 = true, wrd12 = true, wrd24 = true}
end

local function test(opts)
	if not opts then
		opts = {}
	end
	print("Running self-tests.")

	assert(to_binstr(7)=="00000000000000000000000000000111")
	local bs = bitstream{1,1,1,0,0,0,1,1,1,0,0,0}
	assert(bs(4) == 14)
	assert(bs(4) == 3)
	assert(dwords_to_chars({0x41424344,0x31323334}) == "ABCD1234")
	local res = chars_to_dwords("12ABCD")
	assert(res[1] == 0x00003132)
	assert(res[2] == 0x41424344)
	assert(ripemd160("") == "9c1185a5c5e9fc54612808977ee8f548b2258d31", "RIPEMD test 1 failed")
	assert(ripemd160("The quick brown fox jumps over the lazy dog") == "37f332f68db77bd9d7edd4969571ad671cf9dd3b", "RIPEMD test 2 failed")
	assert(sha256("") == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
	assert(sha256("The quick brown fox jumps over the lazy dog") == "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592")

	QR.test()
	if opts.test then --Show test QR code
		local dwords = sha256(os.time() .. tostring({}), "dwords")
		local warn = "!!!!! DO NOT USE THIS PRIVATE KEY FOR ACTUAL BTC STORAGE !!!!!"
		local pkey = btc_privkey(dwords).compressed
		print ("QR code of BTC private key "..pkey..":")
		print (warn)
		print (QR.render(pkey, 6))
		print(warn)
	end

	local sh = new_shifter(0x12345678)
	for i = 1, 100 do
		sh()
	end
	assert(tobit(sh("dump")) == tobit(0x8d8aa8c3))

	local dwords = {1,0}
	assert(bip39(dwords) == "abandon abandon able abandon abandon about")

	local rnd0 = new_random{0,0,0,1,1,1,1,1}
	for i = 1, 990 do
		rnd0()
	end
	local dump = rnd0("dump")
	for i,val in ipairs({0xe69e4882, 0x993ecb5d, 0xba4f982f, 0x0bafb5d9, 0x46c10ce6, 0x033a2504, 0x1e202557, 0xeb54cd93}) do
		assert(tobit(val) == tobit(dump[i]), "bad "..i)
	end
	assert(tohex(rnd0())=="8995132f")

	local key = get256bits(rnd0)
	assert(hex256(key,"-") == "e7ba2240-c5aa7fe7-584a794e-c0ab7d4b-1b74cf7b-ccbaf55d-b5e5b889-1442c646")
	assert(dwords_to_password(key) == "VXEy@N)F?Vm4FVjMaJZi6TjfuPbHRnJumUy54b6h")

	assert(hex256(keymaster("Satan",2),"-") == "16784c4f-eb122684-376d1d73-375adccd-133b10cf-4ef0bac3-abe34427-a09aecd2")
	assert(BIN_TO_ANY.convert(dwords_to_chars({0x12345678,0xffffffff}),"0123456789abcdef") == "12345678ffffffff")
	assert(to_base58({0x80, 0x32247122, 0xF9FF8BB7, 0x8BBEFC55, 0x4E729121, 0x24410788, 0x2417AF0D, 0x77EB7A22, 0x784171F2, 0xAB079763}) == "5JCNQBno4UP562LCEXMTr72WVUe315rrXzPqAFiap8zQNjzarbL")
	assert(checkwords("Homopes") == "devote asthma")
	if opts.no_btc_addr then
		print("Skipping BTC pubkey generation tests.")
	else
		BIGNUM.test()
		local btckeys = btc_privkey(keymaster("Satan",1),"-")
		assert(btckeys.compressed == "Ky63MMQWPEYLpG5rbbSxDbtAwfzaNDvKzH2co6QXKg7mFJHft5TS")
		assert(btckeys.uncompressed == "5JEq7RZWmTdZ8Y4NCv7nb7zp7VmmGEMEpR2Gp9UXtMeL65u7vyv")
		local dwpubkey = privkey_to_pubkey("0x2EE42A735AE3D0C1A7E435EF3B4731B0205A7839015E100BCC8472EE989EC887")
		assert(wif(dwpubkey, "uncompressed") == "1MNQH6Xi8Ltf1TfgDWYNijZaiPdVGxPSZw")
		assert(wif(dwpubkey, "compressed") == "1BMwnCKvHD9KMHa1Acb2BsisMuM1XRwjvU")
	end
	print("All self-tests OK")
end

local function parse_options()
	local allowed = {"difficulty", "salt", "test", "checksum", "no_btc_addr", "prefix", "calibrate", "qr_halfheight", "qr_doublewidth", "qr_character", "qr_invert"}
	for i, opt in ipairs(allowed) do
		allowed[opt] = true
	end

	local opts = {}
	for i, arg in ipairs(arg) do
		if arg:match("=") then
			local opt, val = arg:match("(.-)=(.+)")
			assert(opt and val, "Invalid option syntax: "..arg)
			assert(#opt > 0)
			assert(#val > 0)
			opts[opt] = val
		else
			opts[arg] = true
		end
	end
	for k,v in pairs(opts) do
		if not allowed[k] then
			print("Invalid option: "..k.."="..tostring(v))
			table.sort(allowed)
			print("Allowed options: "..table.concat(allowed,", "))
			os.exit()
		end
	end

	return opts
end

local function main()
	_G.BIGNUM = load_bignum()
	_G.QR = load_qr()
	_G.BIN_TO_ANY = bin_to_any_module()
	print("KRYPTA by Fuxoft, version ".._G.VERSION)
	local opts = parse_options()

	if opts.prefix then
		if opts.prefix:match(":") then
			error("Do NOT include the colon in prefix.")
		end
		if not get_all_prefixes()[opts.prefix] then
			error("Unknown prefix: "..opts.prefix)
		end
	end

	QR.init(opts)
	
	if opts.test then
		test(opts)
		os.exit()
	end

	if opts.calibrate then
		print("Calibrating the difficulty...")
		calibrate()
		os.exit()
	end

	if opts.salt then
		SALT = opts.salt
	end

	if opts.difficulty then
		DIFFICULTY = tonumber(opts.difficulty)
	end

	if DIFFICULTY == 0 then
		print[[
To run Krypta, you must supply at least the 'difficulty' option.
For detailed documentation, visit https://github.com/fuxoft/krypta

All available options with examples:

test
	Do all self tests, print a test QR code (of random BTC private key) and quit.

difficulty=5
	Select the difficulty for master key generation (1 to 31).
	Each subsequent difficulty is twice slower than the previous.
	1 is fastest. 31 takes many years. Use the "calibrate" option
	to find the best difficulty.

calibrate
	Runs a calibration that shows you how much time (approximately) it takes
	to generate the master key for various difficulties.

checksum=0x123
	Specify checksum for your master passphrase (0x and three hex digits).
	Useful to be sure that you entered the passphrase correctly.
	Using it degrades you security a tiny little bit because if the attacker
	knows it, he can easily check if his master passphrase and difficulty guess
	is correct or not.

salt=00420777123456
	Specify salt which is combined with your passphrase to generate master key.
	Note that having passphrase "abc" and salt "def" is not the same thing
	as having passphrase "abcdef" (or "defabc") without salt.

no_btc_addr
	Disables generating BTC addresses (and saves a few seconds of time).
	Note that BTC private keys generation is still enabled because it's fast.
	The BTC address generation algorithm is currently very naive and rather slow.
	It can be significantly improved.

prefix=pwd12
	Automatically sets default prefix. Entering "xyz" as an index then
	automatically selects index "pwd12:xyz". Use index "all:xyz" to show
	all prefixes (the same result as entering index "xyz" when no default
	prefix is set).

The following options are for QR code generation for BTC private keys
and addresses. Use the "test" option to experiment with various QR code options.
If you have recent sane computer, you will probably want to use both "qr_inverse"
and "qr_halfheight" options.
	
qr_halfheight
	Displays the QR code at half height using UTF graphics. Best option
	if your terminal and font support these graphical characters. Using
	this option automatically disables qr_doublewidth and qr_character options.

qr_character=X
	Select character to represent "full" QR code pixels.
	Default is the U+2588 Unicode "full block" character.
	Use this if your terminal / font don't support it.
	The "empty" pixel is always represented by space.

qr_doublewidth
	Use this option to render every pixel as two characters.
	Dumber alternative to "qr_halfheight". The resulting
	QR code is twice as large (in both directions)
	as with "qr_halfheight".

qr_invert
	Inverts the QR display so that full pixels become spaces and spaces become
	full pixels. Note that this is necessary on terminals that display
	white-on-black characters (i.e. most of them).
]]
		os.exit()
	end
	if not DIFFICULTY or (DIFFICULTY < 1 or DIFFICULTY > MAXDIFC or (DIFFICULTY ~= math.floor(DIFFICULTY))) then
		error("Invalid difficulty: "..tostring(DIFFICULTY))
	end

	CHECKSUM = CHECKSUM or tonumber(opts.checksum)

	if CHECKSUM then
		assert(CHECKSUM >= 0 and CHECKSUM <= 0xfff, "Invalid checksum value")
	end

	print("STARTING!")
	test(opts)
	print("SALT='"..SALT.."' ("..#SALT.." characters)")
	assert(type(SALT) == "string", "SALT is not string")
	if #SALT == 0 then
		print("WARNING! 'SALT' is not set. Set it to be more secure.")
	end

	if not CHECKSUM then
		print("Checksum not set, will display it.")
	end
	print("Please enter your super-secret MASTER PASSPHRASE:")
	local masterpp = io.read()
--	print("Please enter it again:")
--	local masterpp2 = io.read()
--	assert(masterpp == masterpp2, "Passphrase mismatch")
	for i = 1, 200 do
		print("")
	end
	if #masterpp < 10 then
		print("WARNING: Master passphrase is very short.")
	end

	local zeroes = dwords_to_chars{0}
	local masterseed = masterpp..zeroes..SALT
	print("Calculating master key at difficulty "..DIFFICULTY)
	local masterkey,time = keymaster(masterseed, DIFFICULTY, true)
	print("Masterkey generated in "..time.." seconds.")
	local chsum = band(0xfff,bxor(masterkey[1],masterkey[7],masterkey[8]))
	print(string.format("Masterkey checksum is: 0x%03x",chsum))
	if CHECKSUM then
		if tobit(CHECKSUM) ~= tobit(chsum) then
			print("!!! CHECKSUM DOES NOT MATCH !!!")
			error("nomatch")
		else
			print("Checksum matches.")
		end
	end
	--print("-masterkey- "..hex256(masterkey," "))
	local strseed0 = dwords_to_chars(masterkey)
	while true do
		print("\n----------------------------------")
		if opts.prefix then
			print("Default prefix is '".. opts.prefix ..":' (override with 'all:')")
		end
		print("Enter index with optional 'prefix:' (default='')")
		local ind0 = assert(io.read())
		local prefix, index = ind0:match("^(.+):(.*)$")
		if opts.prefix and not prefix then
			prefix = opts.prefix
			index = ind0
		end
		if prefix == "all" then
			prefix = nil
			ind0 = index
		end
		local show = get_all_prefixes()

		if index and prefix then
			if not show[prefix] then
				print("Error: Prefix '"..prefix.."' is invalid.")
				show = false
			else
				show = {[prefix] = true}
			end
		else
			--Show everything
			index = ind0
		end

		if index:match(":") then
			print("Error: Colon (':') detected but no valid prefix and index.")
			show = false
		end

		if show then
			print(string.format("Entered index string: '%s' (%s chars)", index, #index))
			if index == "" then
				print("WARNING. Index is empty string.")
			end
			local rnd = new_random(sha256(index..zeroes..strseed0,"dwords"))
			local result = get256bits(rnd)
			assert(#result == 8)
			local ichksum = sha256(strseed0..zeroes..dwords_to_chars(result)..zeroes.."index checksum", "dwords")
			local chw1, chw2 = band(ichksum[1], 0x7ff), band(ichksum[2], 0x7ff)
			if prefix then
				print(string.format("Checkwords for this specific master passphrase, prefix and index (%s:%s): '%s'", prefix, index, checkwords(strseed0..dwords_to_chars(result)..prefix, 3)))
			else
				print(string.format("Checkwords for this specific master passphrase and index (no prefix): '%s'", checkwords(strseed0..dwords_to_chars(result))))
			end

			if show.hex then
				print("(hex:) 256bit hex number: "..hex256(result))
				print("(hex:) With spaces: "..hex256(result," "))
			end
			local pubkey
			if not opts.no_btc_addr and (show.btcc or show.btcu) then
				pubkey = privkey_to_pubkey("0x"..hex256(result))
			end
			local privkeys = btc_privkey(result)
			for ind, typ in ipairs {"compressed", "uncompressed"} do
				local key = "btcc"
				if typ == "uncompressed" then
					key = "btcu"
				end
				if show[key] then
					print(string.format("(%s:) BTC WIF privkey (%s): %s", key, typ, privkeys[typ]))
					if not prefix then
						print(string.format("Specify the %s: prefix to display QR codes.", key))
					else
						print("--- Private key QR code:")
						print(QR.render(privkeys[typ], 4))
						print("--- End of private key QR code")
					end
					if pubkey then
						local wif = wif(pubkey, typ)
						print(string.format("(%s:) Corresponding BTC address (%s): %s", key, typ, wif))
						if prefix then
							print("--- Public BTC address QR code:")
							print(QR.render(wif, 4))
							print("--- End of public BTC address QR code")
						end
					else
						print("("..typ.." BTC address generation disabled by 'no_btc_addr' user option)")
					end
				end
			end
			if show.pwd15 then
				print("(pwd15:) 15 chars password: "..dwords_to_password(result,3))
			end
			if show.pwd40 then
				print("(pwd40:) 40 chars password: "..dwords_to_password(result))
			end
			if show.wrd12 then
				print("(wrd12:) BIP39/12: "..bip39{result[1], result[2], result[3], result[4]})
			end
			if show.wrd24 then
				print("(wrd24:) BIP39/24: "..bip39(result))
			end
		else
			print("Nothing to show. Enter valid prefix or leave the prefix out.")
		end
	end
end

main()
