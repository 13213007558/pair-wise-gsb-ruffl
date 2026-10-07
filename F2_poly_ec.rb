#!/usr/bin/ruby -Wall

require 'F2_poly_mod.rb'
require 'F2_poly_factor.rb'

class F2_poly_ec
	def initialize(a, b, modulus)
		if F2_poly === modulus
			@modulus = modulus
		else
			@modulus = F2_poly.new(modulus)
		end

		unless F2_poly_factor.irr?(@modulus)
			raise "F2_poly_ec: modulus is not irreducible."
		end

		@a = coerce_field_element(a)
		@b = coerce_field_element(b)

		if @b.zero?
			raise "F2_poly_ec: b must be nonzero for a nonsingular curve."
		end
	end

	attr_reader :a, :b, :modulus

	def ==(other)
		F2_poly_ec === other && @modulus == other.modulus &&
			@a == other.a && @b == other.b
	end

	def hash
		[@modulus.bits, @a.residue.bits, @b.residue.bits].hash
	end

	def eql?(other)
		self == other
	end

	def field_degree
		@modulus.degree
	end

	def field_element(value)
		coerce_field_element(value)
	end

	def zero
		F2_poly_mod.new(0, @modulus)
	end

	def one
		F2_poly_mod.new(1, @modulus)
	end

	def infinity
		F2_poly_ec_point.new(self)
	end

	def point(x, y)
		F2_poly_ec_point.new(self, x, y)
	end

	def on_curve?(x, y)
		x = coerce_field_element(x)
		y = coerce_field_element(y)
		y * y + x * y == x * x * x + @a * x * x + @b
	end

	def points
		elements = F2_poly_mod.elements_for_modulus(@modulus)
		affine_points = elements.product(elements).select do |x, y|
			on_curve?(x, y)
		end.collect do |x, y|
			point(x, y)
		end
		[infinity] + affine_points
	end

	def square_root(value)
		value ** (1 << (field_degree - 1))
	end

	def absolute_trace_one?(value)
		trace = value
		frobenius = value
		(field_degree - 1).times do
			frobenius = frobenius * frobenius
			trace = trace + frobenius
		end
		trace.one?
	end

	def solve_artin_schreier(rhs)
		n = field_degree
		rows = Array.new(n, 0)

		n.times do |coordinate|
			element = F2_poly_mod.new(1 << coordinate, @modulus)
			image = element * element + element
			n.times do |row|
				rows[row] |= ((image.residue.bits >> row) & 1) << coordinate
			end
		end

		rows = rows.each_with_index.collect do |row, row_index|
			row | (((rhs.residue.bits >> row_index) & 1) << n)
		end
		pivot_rows = Array.new(n)
		row = 0

		n.times do |column|
			pivot = (row...n).find {|candidate| (rows[candidate] >> column) & 1 == 1}
			next unless pivot
			rows[row], rows[pivot] = rows[pivot], rows[row]
			n.times do |other_row|
				next if other_row == row || ((rows[other_row] >> column) & 1) == 0
				rows[other_row] ^= rows[row]
			end
			pivot_rows[column] = row
			row += 1
		end

		(row...n).each do |inconsistent_row|
			if (rows[inconsistent_row] >> n) & 1 == 1
				return nil
			end
		end

		bits = 0
		n.times do |column|
			pivot_row = pivot_rows[column]
			next unless pivot_row
			bits |= ((rows[pivot_row] >> n) & 1) << column
		end
		F2_poly_mod.new(bits, @modulus)
	end

	def decompress(encoding)
		unless String === encoding
			raise "F2_poly_ec.decompress: expected a compressed point string."
		end

		text = encoding.downcase
		return infinity if text == "00"

		match = /\A0([23])([0-9a-f]+)\z/.match(text)
		unless match
			raise "F2_poly_ec.decompress: malformed compressed point."
		end

		y_bit = match[1] == "3" ? 1 : 0
		x_bits = Integer("0x" + match[2])
		x_polynomial = F2_poly.new(x_bits)
		if !x_polynomial.zero? && x_polynomial.degree >= field_degree
			raise "F2_poly_ec.decompress: x is outside the field."
		end

		x = F2_poly_mod.new(x_polynomial, @modulus)
		if x.zero?
			return point(x, square_root(@b))
		end

		rhs = x + @a + @b / (x * x)
		if absolute_trace_one?(rhs)
			raise "F2_poly_ec.decompress: no point has this x coordinate."
		end

		z = solve_artin_schreier(rhs)
		if z.nil?
			raise "F2_poly_ec.decompress: no point has this x coordinate."
		end
		z = z + one if z.residue[0] != y_bit
		point(x, x * z)
	end

	def read_compressed(encoding)
		decompress(encoding)
	end

	private

	def coerce_field_element(value)
		if F2_poly_mod === value
			unless value.modulus == @modulus
				raise "F2_poly_ec: field element has a different modulus."
			end
			value
		else
			F2_poly_mod.new(value, @modulus)
		end
	end
end

class F2_poly_ec_point
	def initialize(curve, x = nil, y = nil)
		unless F2_poly_ec === curve
			raise "F2_poly_ec_point: expected an F2_poly_ec curve."
		end
		if x.nil? != y.nil?
			raise "F2_poly_ec_point: x and y must both be given or both omitted."
		end

		@curve = curve
		if x.nil?
			@x = nil
			@y = nil
		else
			@x = curve.field_element(x)
			@y = curve.field_element(y)
			unless curve.on_curve?(@x, @y)
				raise "F2_poly_ec_point: (#{@x}, #{@y}) is not on the curve."
			end
		end
	end

	attr_reader :curve, :x, :y

	def infinity?
		@x.nil?
	end

	def to_s
		return "O" if infinity?
		"(#{@x}, #{@y})"
	end

	def inspect
		to_s
	end

	def ==(other)
		return false unless F2_poly_ec_point === other && @curve == other.curve
		if infinity?
			other.infinity?
		else
			!other.infinity? && @x == other.x && @y == other.y
		end
	end

	def hash
		[@curve, @x&.residue, @y&.residue].hash
	end

	def eql?(other)
		self == other
	end

	def -@
		return self.dup if infinity?
		@curve.point(@x, @x + @y)
	end

	def +(other)
		same_curve!(other)
		return other.dup if infinity?
		return self.dup if other.infinity?
		return double if @x == other.x && @y == other.y
		return @curve.infinity if @x == other.x

		lambda_value = (@y + other.y) / (@x + other.x)
		x3 = lambda_value * lambda_value + lambda_value + @x + other.x + @curve.a
		y3 = lambda_value * (@x + x3) + x3 + @y
		@curve.point(x3, y3)
	end

	def double
		return @curve.infinity if infinity? || @x.zero?

		lambda_value = @x + @y / @x
		x3 = lambda_value * lambda_value + lambda_value + @curve.a
		y3 = @x * @x + (lambda_value + @curve.one) * x3
		@curve.point(x3, y3)
	end

	def scalar_mul(scalar)
		unless Integer === scalar
			raise "F2_poly_ec_point.scalar_mul: expected an integer."
		end

		result = @curve.infinity
		return result if scalar == 0

		addend = self
		n = scalar.abs
		while n > 0
			result = result + addend if (n & 1) == 1
			addend = addend.double
			n >>= 1
		end
		scalar < 0 ? -result : result
	end

	def *(scalar)
		scalar_mul(scalar)
	end

	def coerce(other)
		return [self, other] if Integer === other
		raise "F2_poly_ec_point: cannot coerce #{other.class}."
	end

	def compress
		return "00" if infinity?
		if @x.zero?
			y_bit = 1
		else
			y_bit = (@y / @x).residue[0]
		end
		format("0%d%x", 2 + y_bit, @x.residue.bits)
	end

	def to_compressed_s
		compress
	end

	def write_compressed
		compress
	end

	private

	def same_curve!(other)
		unless F2_poly_ec_point === other && @curve == other.curve
			raise "F2_poly_ec_point: points are on different curves."
		end
	end
end
