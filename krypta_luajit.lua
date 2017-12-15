#!/usr/bin/env luajit
--version 20171215

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

local MAXDIFC = 31

local bxor, band, bor, ror, rol, tohex, tobit, bnot, rshift, lshift = bit.bxor, bit.band, bit.bor, bit.ror, bit.rol, bit.tohex, bit.tobit, bit.bnot, bit.rshift, bit.lshift

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

local privkey_to_pubkey = function(secret)
	assert(#secret > 30)
	local new = BIGNUM.new
	local zero = BIGNUM.zero
	local one = new(1)
	local two = new(2)
	local three = new(3)
	local p = new("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F")
	local g = {x=new("0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"), y=new("0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8")}
	local order = new("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141")
	secret = new(secret)

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
		io.write("Calculating BTC pubkey (32 steps)")
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
	local pubkey = mult(g, secret)
	return {x=BIGNUM.to_dwords(pubkey.x,8), y=BIGNUM.to_dwords(pubkey.y,8)}	
end

BIGNUM = load_bignum()

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

local function test(opts)
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
	if opts.no_btc then
		print("Skipping BTC tests.")
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
	local allowed = {"difficulty", "salt", "test", "checksum", "no_btc"}
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
	BIN_TO_ANY = bin_to_any_module()
	local opts = parse_options()
	if opts.test then
		test(opts)
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
		print("Enter index with optional 'prefix:' (default='')")
		local ind0 = assert(io.read())
		local prefix, index = ind0:match("^(.+):(.+)$")
		local show = {hex = true, btcc = true, btcu = true, pwd15 = true, pwd40 = true, wrd12 = true, wrd24 = true}

		if index then
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
			local rnd = new_random(sha256(index..zeroes..strseed0,"dwords"))
			local result = get256bits(rnd)
			assert(#result == 8)
			local ichksum = sha256(strseed0..zeroes..dwords_to_chars(result)..zeroes.."index checksum", "dwords")
			local chw1, chw2 = band(ichksum[1], 0x7ff), band(ichksum[2], 0x7ff)
			if prefix then
				print(string.format("Checkwords for this specific master passphrase, index and prefix: '%s'", checkwords(strseed0..dwords_to_chars(result)..prefix, 3)))
			else
				print(string.format("Checkwords for this specific master passphrase and index: '%s'", checkwords(strseed0..dwords_to_chars(result))))
			end

			if show.hex then
				print("(hex:) 256bit hex number: "..hex256(result))
				print("(hex:) With spaces: "..hex256(result," "))
			end
			local pubkey
			if not opts.no_btc and (show.btcc or show.btcu) then
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
					if pubkey then
						print(string.format("(%s:) Corresponding BTC address (%s): %s", key, typ, wif(pubkey, typ)))
					else
						print("("..typ.." BTC address generation disabled by 'no_btc' user option)")
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
