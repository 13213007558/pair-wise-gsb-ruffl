#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# John Kerl
# kerl.john.r@gmail.com
# Copyright (c) 2004
# Ported to Ruby 2011-02-10
# ================================================================

require 'F2_poly.rb'
require 'F2_poly_factor.rb'
require 'Int_factor.rb'

class F2_poly_mod
	# ----------------------------------------------------------------
	def initialize(residue, modulus)
		if F2_poly === residue
			@residue = residue
		else
			@residue = F2_poly.new(residue)
		end
		if F2_poly === modulus
			@modulus = modulus
		else
			@modulus = F2_poly.new(modulus)
		end

		@residue = @residue % @modulus
	end

	attr_accessor :residue
	attr_reader   :modulus

	# ----------------------------------------------------------------
	def to_s()
		@residue.to_s
	end
	def inspect()
		@residue.inspect + "@" + @modulus.inspect
	end

	# ----------------------------------------------------------------
	def ==(other)
		@residue == other.residue and @modulus == other.modulus
	end

	def zero?
		return @residue.zero?
	end
	def one?
		return @residue.one?
	end

	# ----------------------------------------------------------------
	def +(other)
		F2_poly_mod.new((@residue + other.residue) % @modulus, @modulus)
	end
	def -(other)
		F2_poly_mod.new((@residue - other.residue) % @modulus, @modulus)
	end
	def -@
		F2_poly_mod.new((-@residue) % @modulus, @modulus)
	end
	def *(other)
		F2_poly_mod.new((@residue * other.residue) % @modulus, @modulus)
	end

	# See the section "Second reciprocation method" (3.10) in my
	# document "Computation in finite fields".
	# Let r = residue and m = modulus.  We want 1/r mod m.
	# Using extended GCD, we find g, s, and t such that
	#   g = s *r + t * m
	# If g != 1, then r is not invertible.  If g == 1, then
	#   1 = s * r (mod m)
	# and so the reciprocal is s.
	def recip
		g, s, t = @residue.ext_gcd(@modulus)
		if !g.one?
			raise "F2_poly_mod.recip: division by zero."
		end
		return F2_poly_mod.new(s, @modulus)
	end

	def /(other)
		self * other.recip
	end

	def **(e)
		if @residue.zero?
			if e == 0
				raise "Int_mod:  0**0 undefined."
			elsif e < 0
				raise "Int_mod **:  division by zero.."
			else
				return F2_poly_mod.new(0, @modulus)
			end
		end

		rv = F2_poly_mod.new(1, @modulus)
		xp = F2_poly_mod.new(@residue, @modulus)
		if e < 0
			xp = xp.recip
			e = -e
		end

		# Repeated squaring
		while (e != 0)
			if (e & 1) == 1
				rv *= xp;
			end
			e = e >> 1;
			xp *= xp;
		end
		return rv
	end

	# ----------------------------------------------------------------
	def F2_poly_mod.elements_for_modulus(m)
		if not F2_poly === m
			m = F2_poly.new(m)
		end
		max_bits = (1 << m.degree) - 1
		(0..max_bits).collect{|a| F2_poly_mod.new(F2_poly.new(a), m)}
	end
	def F2_poly_mod.units_for_modulus(m) # m should be F2_poly
		if not F2_poly === m
			m = F2_poly.new(m)
		end
		max_bits = (1 << m.degree) - 1
		units = []
		(0..max_bits).each do |j|
			a = F2_poly.new(j)
			if m.gcd(a).one?
				units.push F2_poly_mod.new(a, m)
			end
		end
		units
	end

end

# An isomorphism F2[x]/<source_modulus> -> F2[x]/<target_modulus>.
# Both moduli must be irreducible and have the same degree.  The
# isomorphism is determined by choosing the image beta of the source
# class x; beta must be a root of the source modulus in the target field.
# An element a(x) is then sent to a(beta), rather than reusing its bit
# pattern.  When f has degree n, the n roots beta, beta^2, ...,
# beta^(2^(n-1)) give n isomorphisms for n > 1.
class F2_field_isomorphism
	def initialize(source_modulus, target_modulus, image = :auto)
		@source_modulus = F2_field_isomorphism.coerce_modulus(source_modulus)
		@target_modulus = F2_field_isomorphism.coerce_modulus(target_modulus)
		validate_fields

		@source_generator = F2_poly_mod.new(F2_poly.new(2), @source_modulus)
		if image.equal?(:auto)
			@image, @selection_basis = choose_lowest_root
			@selection_reason = "lowest canonical bit encoding among " \
				"target-field roots of #{@source_modulus}"
		else
			@image = coerce_image(image)
			validate_root(@image)
			@selection_basis = nil
			@selection_reason = "explicitly supplied image"
		end
		@inverse_rows = nil
	end

	attr_reader :source_modulus, :target_modulus, :source_generator,
		:image, :selection_basis, :selection_reason

	def map(element)
		element = coerce_field_element(element, @source_modulus)
		F2_field_isomorphism.evaluate_polynomial(
			element.residue, @image)
	end

	def unmap(element)
		element = coerce_field_element(element, @target_modulus)
		coefficients = solve_linear_isomorphism(element.residue.bits)
		F2_poly_mod.new(F2_poly.new(coefficients), @source_modulus)
	end

	def call(element)
		map(element)
	end

	private

	def F2_field_isomorphism.coerce_modulus(modulus)
		if F2_poly_mod === modulus
			return modulus.modulus
		elsif F2_poly === modulus
			return modulus
		else
			return F2_poly.new(modulus)
		end
	end

	def validate_fields
		source_degree = @source_modulus.degree
		target_degree = @target_modulus.degree
		if source_degree != target_degree
			raise ArgumentError, "field degrees differ: " \
				"#{source_degree} != #{target_degree}"
		end
		unless F2_poly_factor.irr?(@source_modulus)
			raise ArgumentError, "source modulus is not irreducible: " \
				"#{@source_modulus}"
		end
		unless F2_poly_factor.irr?(@target_modulus)
			raise ArgumentError, "target modulus is not irreducible: " \
				"#{@target_modulus}"
		end
	end

	def choose_lowest_root
		root = find_any_root
		root_bits = frobenius_orbit(root).collect do |orbit_root|
			orbit_root.residue.bits
		end.sort
		selected = F2_poly_mod.new(F2_poly.new(root_bits.first),
			@target_modulus)
		basis = {
			:rule => :lowest_canonical_root,
			:candidate_order => :ascending_bit_encoding,
			:root_isolation => :frobenius_trace_gcd,
			:roots => root_bits,
			:root_count => root_bits.length,
			:selected_rank => 0,
			:selected_image => root_bits.first
		}
		return selected, basis
	end

	def frobenius_orbit(root)
		orbit = []
		current = root
		@target_modulus.degree.times do
			orbit.push(current)
			current = current * current
		end
		orbit
	end

	def find_any_root
		factor = source_polynomial_over_target
		factor = isolate_linear_factor(factor)
		factor[0]
	end

	def source_polynomial_over_target
		zero = F2_poly_mod.new(0, @target_modulus)
		one = F2_poly_mod.new(1, @target_modulus)
		(@source_modulus.degree + 1).times.collect do |j|
			@source_modulus[j] == 1 ? one : zero
		end
	end

	def isolate_linear_factor(factor)
		return factor if extension_poly_degree(factor) == 1

		left, right = trace_split(factor)
		left_degree = extension_poly_degree(left)
		right_degree = extension_poly_degree(right)
		chosen = left_degree <= right_degree ? left : right
		isolate_linear_factor(chosen)
	end

	def trace_split(factor)
		one = F2_poly_mod.new(1, @target_modulus)
		target_x = F2_poly_mod.new(F2_poly.new(2), @target_modulus)
		a = one

		@target_modulus.degree.times do
			trace = trace_remainder(a, factor)
			left = extension_poly_gcd(factor, trace)
			left_degree = extension_poly_degree(left)
			if left_degree > 0 && left_degree < extension_poly_degree(factor)
				trace_plus_one = extension_poly_add(trace, [one])
				right = extension_poly_gcd(factor, trace_plus_one)
				return left, right
			end
			a = a * target_x
		end

		raise RuntimeError, "F2_field_isomorphism: could not split source " \
			"polynomial in the target field."
	end

	def trace_remainder(a, divisor)
		zero = F2_poly_mod.new(0, @target_modulus)
		h = [zero, a]
		trace = [zero]
		@target_modulus.degree.times do
			trace = extension_poly_add(trace, h)
			h = extension_poly_frobenius(h, divisor)
		end
		extension_poly_mod(trace, divisor)
	end

	def extension_poly_degree(poly)
		extension_poly_normalize(poly)
		poly.empty? ? -1 : poly.length - 1
	end

	def extension_poly_normalize(poly)
		poly.pop while !poly.empty? && poly.last.zero?
		poly
	end

	def extension_poly_add(left, right)
		zero = F2_poly_mod.new(0, @target_modulus)
		size = [left.length, right.length].max
		size.times.collect do |j|
			(left[j] || zero) + (right[j] || zero)
		end
	end

	def extension_poly_mod(poly, divisor)
		zero = F2_poly_mod.new(0, @target_modulus)
		remainder = poly.collect {|coefficient| coefficient || zero}
		divisor = extension_poly_normalize(divisor.collect {|c| c})
		divisor_degree = extension_poly_degree(divisor)

		while extension_poly_degree(remainder) >= divisor_degree
			degree = extension_poly_degree(remainder)
			leading = remainder[degree] / divisor.last
			shift = degree - divisor_degree
			divisor.each_with_index do |coefficient, j|
				next if coefficient.zero?
				remainder[shift + j] ||= zero
				remainder[shift + j] =
					remainder[shift + j] + (leading * coefficient)
			end
			extension_poly_normalize(remainder)
		end
		remainder
	end

	def extension_poly_gcd(left, right)
		left = extension_poly_normalize(left.collect {|coefficient| coefficient})
		right = extension_poly_normalize(right.collect {|coefficient|
			coefficient})
		while !right.empty? && right.any? {|coefficient|
			!coefficient.nil? && !coefficient.zero?}
			left, right = right, extension_poly_mod(left, right)
		end
		return [] if left.empty?
		leading = left.last
		return left if leading.one?
		inverse = leading.recip
		left.collect {|coefficient| coefficient * inverse}
	end

	def extension_poly_frobenius(poly, divisor)
		zero = F2_poly_mod.new(0, @target_modulus)
		squared = []
		poly.each_with_index do |coefficient, j|
			next if coefficient.nil? || coefficient.zero?
			squared[2 * j] = (squared[2 * j] || zero) + (coefficient * coefficient)
		end
		extension_poly_mod(squared, divisor)
	end

	def coerce_image(image)
		if F2_poly_mod === image
			unless image.modulus == @target_modulus
				raise ArgumentError, "image modulus does not match target " \
					"modulus"
			end
			return image
		elsif F2_poly === image
			return F2_poly_mod.new(image, @target_modulus)
		else
			return F2_poly_mod.new(image, @target_modulus)
		end
	rescue ArgumentError, TypeError
		raise ArgumentError, "invalid target-field image"
	end

	def validate_root(candidate)
		value = F2_field_isomorphism.evaluate_polynomial(
			@source_modulus, candidate)
		unless value.zero?
			raise ArgumentError, "#{candidate} is not a target-field root " \
				"of source modulus #{@source_modulus}"
		end
	end

	def coerce_field_element(element, modulus)
		if F2_poly === element
			element = F2_poly_mod.new(element, modulus)
		elsif not F2_poly_mod === element
			begin
				element = F2_poly_mod.new(element, modulus)
			rescue ArgumentError, TypeError
				raise ArgumentError, "expected an F2_poly_mod field element"
			end
		end
		unless element.modulus == modulus
			raise ArgumentError, "field element does not use the expected " \
				"modulus #{modulus}"
		end
		element
	end

	def F2_field_isomorphism.evaluate_polynomial(polynomial, point)
		bits = polynomial.bits
		degree = F2_poly.bit_degree(bits)
		value = F2_poly_mod.new(0, point.modulus)
		one = F2_poly_mod.new(1, point.modulus)
		degree.downto(0) do |j|
			value = value * point
			if ((bits >> j) & 1) == 1
				value = value + one
			end
		end
		value
	end

	def solve_linear_isomorphism(target_bits)
		rows = inverse_rows
		n = @target_modulus.degree
		coefficients = 0
		n.times do |coefficient|
			if Bit_arith.ones(rows[coefficient] & target_bits).odd?
				coefficients |= 1 << coefficient
			end
		end
		coefficients
	end

	def inverse_rows
		return @inverse_rows unless @inverse_rows.nil?

		n = @target_modulus.degree
		columns = []
		power = F2_poly_mod.new(1, @target_modulus)
		n.times do |j|
			columns[j] = power.residue.bits
			power = power * @image
		end

		identity_mask = (1 << n) - 1
		rows = Array.new(n, 0)
		n.times do |coefficient|
			n.times do |basis|
				if ((columns[basis] >> coefficient) & 1) == 1
					rows[coefficient] |= 1 << basis
				end
			end
			rows[coefficient] |= 1 << (n + coefficient)
		end

		n.times do |column|
			pivot = (column...n).detect do |row|
				((rows[row] >> column) & 1) == 1
			end
			raise RuntimeError, "chosen root does not span the target field" \
				if pivot.nil?
			rows[column], rows[pivot] = rows[pivot], rows[column] unless pivot == column
			(0...n).each do |row|
				next if row == column
				if ((rows[row] >> column) & 1) == 1
					rows[row] ^= rows[column]
				end
			end
		end

		@inverse_rows = rows.collect {|row| (row >> n) & identity_mask}
	end
end

def F2_poly_mod.field_isomorphism(source_modulus, target_modulus,
	image = :auto)
	F2_field_isomorphism.new(source_modulus, target_modulus, image)
end
