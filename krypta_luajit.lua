#!/usr/bin/env luajit

--[[
	Set the SALT to something you can easily remember.
	For example your e-mail, your phone number or your full date of birth.
	It can be fairly obvious info, known to people around you
	but it should be fairly unique
	so it SHOULD NOT be the name of your pet or your favorite food or color.
]]
local SALT = "" --Put the SALT between the quotes.
local DIFFICULTY = 0 --Put desired difficulty here
local CHECKSUM = 0x12345678 --Put checksum here

--RSA256 implementation from https://github.com/JustAPerson/LuaCrypt/

local MAXDIFC = 31

local bxor, band, bor, ror, rol, tohex, tobit, bnot, rshift, lshift = bit.bxor, bit.band, bit.bor, bit.ror, bit.rol, bit.tohex, bit.tobit, bit.bnot, bit.rshift, bit.lshift

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

local function to_bin(n)
	local res = {}
	for i = 1,32 do
		n = rol(n,1)
		res[i] = band(n,1)
	end
	return table.concat(res)
end

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
	local padding = 64 - ((length + 9) % 64);
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

local function test()
	assert(to_bin(7)=="00000000000000000000000000000111")
	assert(dwords_to_chars({0x41424344,0x31323334}) == "ABCD1234")
	assert(sha256("") == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
	assert(sha256("The quick brown fox jumps over the lazy dog") == "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592")
	local sh = new_shifter(0x12345678)
	for i = 1, 100 do
		sh()
	end
	assert(tobit(sh("dump")) == tobit(0x8d8aa8c3))

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
end

local function parse_options()
	local allowed = {"difficulty", "salt", "test", "checksum"}
	for i, opt in ipairs(allowed) do
		allowed[opt] = true
	end

	local opts = {}
	for i, arg in ipairs(arg) do
		if arg:match("=") then
			local opt, val = arg:match("(.-)=(.+)")
			assert(opt and val)
			assert(#opt > 0)
			assert(#val > 0)
			opts[opt] = val
		else
			opts[arg] = true
		end
	end
	for k,v in pairs(opts) do
		if not allowed[k] then
			error("Invalid option: "..k.."="..tostring(v))
		end
	end
	return opts
end

local function main()
	local opts = parse_options()
	if opts.test then
		test()
		print("All self-tests OK")
		os.exit()
	end

	if opts.salt then
		SALT = opts.salt
	end

	if opts.difficulty then
		DIFFICULTY = tonumber(opts.difficulty)
	end

	if DIFFICULTY < 0 or DIFFICULTY > MAXDIFC or (DIFFICULTY ~= math.floor(DIFFICULTY)) then
		error("Invalid difficulty: "..DIFFICULTY)
	end

	if DIFFICULTY == 0 then
		print("Difficulty not set, calibrating...")
		calibrate()
		os.exit()
	end

	if CHECKSUM == 0x12345678 then
		CHECKSUM = nil
	end

	CHECKSUM = CHECKSUM or tonumber(opts.checksum)

	print("STARTING!")
	test()
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
	print("Please enter it again:")
	local masterpp2 = io.read()
	assert(masterpp == masterpp2, "Passphrase mismatch")
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
	local chsum = band(0xffff,bxor(masterkey[1],masterkey[7],masterkey[8]))
	print(string.format("Masterkey checksum is: 0x%04x",chsum))
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
		print("Enter index (default='0')")
		local index = io.read() or "0"
		local rnd = new_random(sha256(index..zeroes..strseed0,"dwords"))
		local result = get256bits(rnd)
		assert(#result == 8)
		print("256bit hex number: "..hex256(result))
		print("With spaces: "..hex256(result," "))
		print("40 chars password: "..dwords_to_password(result))
		print("15 chars password: "..dwords_to_password(result,3))
	end
end

main()
