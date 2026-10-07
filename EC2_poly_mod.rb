#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# John Kerl
# kerl.john.r@gmail.com
# Copyright (c) 2011
# ================================================================

require 'F2_poly.rb'
require 'F2_poly_mod.rb'
require 'F2_poly_factor.rb'

# ----------------------------------------------------------------
# Non-singular elliptic curves over binary fields GF(2^m):
#
#   E: y^2 + x y = x^3 + a x^2 + b,
#
# with the irreducible defining polynomial f of degree m supplied
# at construction time.  All field arithmetic is delegated to the
# existing F2_poly / F2_poly_mod tools; this file only implements
# the characteristic-2 group law.  In particular, the odd-prime
# formulas (slope = (3x^2+a)/(2y), ...) do NOT apply here.
#
# This code is intended for small-field teaching and back-end
# algorithm verification.  It is not constant-time and makes no
# claim of production cryptographic safety.

class EC2_poly_mod_curve
	# m is the irreducible defining polynomial f(t) for GF(2^m).
	def initialize(a, b, m)
		m = F2_poly.new(m) unless F2_poly === m
		if m.degree < 1
			raise "EC2_poly_mod_curve: field modulus must have positive degree."
		end
		if !F2_poly_factor.irr?(m)
			raise "EC2_poly_mod_curve: #{m} is not irreducible over F2."
		end

		a = F2_poly_mod.new(a, m) unless F2_poly_mod === a
		b = F2_poly_mod.new(b, m) unless F2_poly_mod === b
		if a.modulus != m or b.modulus != m
			raise "EC2_poly_mod_curve: coefficients must be elements of the specified field."
		end

		# The curve is non-singular exactly when b != 0.
		if b.zero?
			raise "EC2_poly_mod_curve: singular curve (b = 0)."
		end

		@a = a
		@b = b
		@m = m
		@degree = m.degree
	end

	attr_reader :a, :b, :m, :degree

	def to_s
		"y^2+xy=x^3+(#{@a})x^2+(#{@b}) over GF(2^#{@degree}) mod #{@m}"
	end
	def inspect
		"#{@a},#{@b}@#{@m}"
	end

	def ==(other)
		EC2_poly_mod_curve === other and @a == other.a and @b == other.b \
			and @m == other.m
	end

	# Coerce an integer/string/F2_poly/F2_poly_mod scalar to an
	# element of this field.
	def elem(v)
		if F2_poly_mod === v
			if v.modulus != @m
				raise "EC2_poly_mod_curve: field modulus mismatch."
			end
			return v
		end
		F2_poly_mod.new(v, @m)
	end

	def infinity
		EC2_poly_mod_point.new(nil, nil, self, true)
	end

	def point(x, y)
		EC2_poly_mod_point.new(elem(x), elem(y), self, false)
	end

	# ------------------------------------------------------------
	# Curve membership for affine coordinates.  Uses only
	# characteristic-2 field operations.
	def contains?(x, y)
		x = elem(x) unless F2_poly_mod === x
		y = elem(y) unless F2_poly_mod === y
		y*y + x*y == x*x*x + @a*x*x + @b
	end

	# ------------------------------------------------------------
	# Absolute trace Tr: GF(2^m) -> GF(2),
	#   Tr(z) = z + z^2 + z^4 + ... + z^{2^{m-1}}.
	def trace(z)
		z = elem(z) unless F2_poly_mod === z
		t = self.elem(0)
		@degree.times do
			t = t + z
			z = z * z
		end
		t.residue.bits
	end

	# Half-trace for odd m:
	#   H(z) = z + z^4 + z^16 + ... + z^{2^{m-1}},
	# satisfying H(z)^2 + H(z) = z + Tr(z).  Exposed for
	# teaching; roots_for_x uses the general Gaussian solver
	# below so that even m is supported as well.
	def half_trace(z)
		z = elem(z) unless F2_poly_mod === z
		t = self.elem(0)
		zz = z
		i = 1
		while i < @degree
			t = t + zz
			zz = zz * zz * zz * zz
			i += 2
		end
		t + zz
	end

	# Solve z^2 + z = c over GF(2^m) for any m.  The map
	# L(z) = z^2 + z is F2-linear with kernel {0, 1}, so the
	# system is solved by Gaussian elimination on its m x m
	# F2-matrix.  Returns one root z0, or nil when the system is
	# inconsistent (equivalently Tr(c) == 1).  The other root is
	# z0 + 1.
	def artin_schreier_root(c)
		c = elem(c) unless F2_poly_mod === c
		return nil if trace(c) == 1

		n = @degree
		f = @m
		# Build augmented rows, bit-packed into integers: bit j is
		# the coefficient of basis vector t^j, bit n is the RHS.
		rows = Array.new(n, 0)
		(0...n).each do |j|
			ej = F2_poly_mod.new(F2_poly.new(1 << j), f)
			v = (ej * ej + ej).residue.bits
			(0...n).each do |i|
				rows[i] |= ((v >> i) & 1) << j
			end
		end
		cbits = c.residue.bits
		(0...n).each do |i|
			rows[i] |= ((cbits >> i) & 1) << n
		end

		# Gauss-Jordan elimination.
		pivot_col_for_row = {}
		r = 0
		col = 0
		while r < n and col < n
			pivot = (r...n).find {|i| ((rows[i] >> col) & 1) == 1}
			if pivot.nil?
				col += 1
				next
			end
			rows[r], rows[pivot] = rows[pivot], rows[r] unless pivot == r
			(0...n).each do |i|
				next if i == r
				rows[i] ^= rows[r] if ((rows[i] >> col) & 1) == 1
			end
			pivot_col_for_row[r] = col
			r += 1
			col += 1
		end

		coef_mask = (1 << n) - 1
		(r...n).each do |i|
			return nil if (rows[i] & coef_mask) == 0 and rows[i] != 0
		end

		zbits = 0
		pivot_col_for_row.each do |row_index, pivot_col|
			zbits |= ((rows[row_index] >> n) & 1) << pivot_col
		end
		F2_poly_mod.new(F2_poly.new(zbits), f)
	end

	# For x != 0 the curve equation, divided by x^2 with
	# z = y/x, is the Artin-Schreier equation
	#   z^2 + z = x + a + b/x^2 =: rhs.
	# It is solvable iff Tr(rhs) == 0.  Returns [y0, y1], the
	# two roots for y, or nil when no root exists.  For x == 0
	# use y_for_x0 instead.
	def roots_for_x(x)
		x = elem(x) unless F2_poly_mod === x
		rhs = x + @a + @b / (x * x)
		z0 = artin_schreier_root(rhs)
		return nil if z0.nil?

		y0 = x * z0
		[y0, y0 + x]
	end

	# For x = 0 the equation reduces to y^2 = b, which has the
	# unique solution y = b^{2^{m-1}} (Frobenius square root).
	def y_for_x0
		y = @b
		(@degree - 1).times { y = y * y }
		y
	end

	# Enumerate all affine points on the curve.
	def points
		pts = []
		F2_poly_mod.elements_for_modulus(@m).each do |x|
			if x.zero?
				y = y_for_x0
				pts << point(x, y)
			else
				ypair = roots_for_x(x)
				next if ypair.nil?
				ypair.each {|y| pts << point(x, y)}
			end
		end
		pts
	end

	# ------------------------------------------------------------
	# Compressed form (SEC 1 style):
	#   infinity  -> "O"
	#   x == 0    -> "00:<y>", since y^2 = b has a unique root
	#   x != 0    -> "<x>:0" or "<x>:1", where the bit is the
	#               least-significant coefficient of y/x
	def decompress(text)
		text = text.to_s.strip
		return infinity if text == 'O' or text == '00'

		xs, bs = text.split(':')
		if xs.nil? or bs.nil? or xs.empty? or bs.empty? or text.count(':') != 1
			raise "EC2_poly_mod_curve.decompress: malformed '#{text}'."
		end
		x = safe_elem(xs, text)

		if x.zero?
			# The full y is stored; there is no second choice.
			y = safe_elem(bs, text)
			raise "EC2_poly_mod_curve.decompress: (0,#{y}) is not on the curve." \
				unless contains?(x, y)
			return point(x, y)
		end

		bit = parse_hex_int(bs)
		raise "EC2_poly_mod_curve.decompress: malformed '#{text}'." if bit.nil?
		raise "EC2_poly_mod_curve.decompress: bit must be 0 or 1." if bit != 0 and bit != 1
		ypair = roots_for_x(x)
		return nil if ypair.nil? # No points with this x-coordinate.
		y0, y1 = ypair
		# Normalize the ordering so bit 0/1 is well-defined: the
		# root whose y/x has constant coefficient 0 gets bit 0.
		ordered = [y0, y1].sort_by {|y| (y / x).residue.bits & 1}
		point(x, ordered[bit])
	end

	# Same as decompress but raises when the x-coordinate has no points.
	def decompress!(text)
		p = decompress(text)
		raise "EC2_poly_mod_curve.decompress!: no point for '#{text}'." if p.nil?
		p
	end

	# ------------------------------------------------------------
	# Characteristic-2 group law (affine).  See, e.g., Washington,
	# "Elliptic Curves: Number Theory and Cryptography", ch. 5.
	def add(p, q)
		return q if p.infinity?
		return p if q.infinity?
		if p.curve != self or q.curve != self
			raise "EC2_poly_mod_curve.add: points are on different curves."
		end

		x1, y1 = p.x, p.y
		x2, y2 = q.x, q.y

		if x1 == x2
			# P + (-P) = O, where -P = (x, x+y).
			return infinity if y1 == x2 + y2
			return double(p)
		end

		lambda_ = (y1 + y2) / (x1 + x2)
		x3 = lambda_*lambda_ + lambda_ + x1 + x2 + @a
		y3 = lambda_*(x1 + x3) + x3 + y1
		point(x3, y3)
	end

	def negate(p)
		return infinity if p.infinity?
		point(p.x, p.x + p.y)
	end

	def double(p)
		return infinity if p.infinity?
		x1, y1 = p.x, p.y
		# On a non-singular binary curve the unique point of
		# order 2 has x = 0; 2P = O there.
		return infinity if x1.zero?

		lambda_ = x1 + y1 / x1
		x3 = lambda_*lambda_ + lambda_ + @a
		y3 = x1*x1 + lambda_*x3 + x3
		point(x3, y3)
	end

	def mul(k, p)
		if k < 0
			k = -k
			p = negate(p)
		end
		r = infinity
		while k > 0
			r = add(r, p) if (k & 1) == 1
			p = double(p)
			k >>= 1
		end
		r
	end

	private

	def parse_hex_int(s)
		return nil unless s =~ /\A[0-9a-fA-F]+\z/
		Integer("0x" + s)
	end

	def safe_elem(s, text)
		if s !~ /\A[0-9a-fA-F]+\z/
			raise "EC2_poly_mod_curve.decompress: malformed '#{text}'."
		end
		elem(s)
	end
end

# ----------------------------------------------------------------
class EC2_poly_mod_point
	def initialize(x, y, curve, is_infinity = false)
		@curve = curve
		if is_infinity
			@x = nil
			@y = nil
			@infinity = true
			return
		end

		x = curve.elem(x) unless F2_poly_mod === x
		y = curve.elem(y) unless F2_poly_mod === y
		if !curve.contains?(x, y)
			raise "EC2_poly_mod_point: (#{x}, #{y}) is not on #{curve}."
		end
		@x = x
		@y = y
		@infinity = false
	end

	attr_reader :x, :y, :curve

	def infinity?
		@infinity
	end

	def to_s
		return "O" if @infinity
		"(#{@x}, #{@y})"
	end
	def inspect
		to_s
	end

	def ==(other)
		return false unless EC2_poly_mod_point === other
		return @curve == other.curve if @infinity and other.infinity?
		return false if @infinity or other.infinity?
		@curve == other.curve and @x == other.x and @y == other.y
	end
	alias eql? ==

	def hash
		[@x, @y, @infinity].hash
	end

	def +(other)
		@curve.add(self, other)
	end
	def -(other)
		@curve.add(self, @curve.negate(other))
	end
	def -@
		@curve.negate(self)
	end
	def *(k)
		@curve.mul(k, self)
	end

	# Allow scalar-first notation, e.g. 7 * P.
	def coerce(other)
		Integer === other ? [self, other] : nil
	end

	# SEC 1-style compression; inverse is curve.decompress.
	def compress
		return "O" if @infinity
		return "00:#{@y}" if @x.zero?
		bit = (@y / @x).residue.bits & 1
		"#{@x}:#{bit}"
	end

	# Enumeration helper: the two points sharing an x-coordinate
	# are P and -P = (x, x+y).
end
