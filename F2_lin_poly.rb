#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# ================================================================

require 'F2_poly.rb'
require 'F2_poly_mod.rb'
require 'Bit_matrix.rb'

# ================================================================
# Linearized polynomials (a.k.a. q-additive or Frobenius polynomials)
# over a binary extension field:
#
#   L(x) = a_0 x + a_1 x^2 + a_2 x^4 + ... + a_d x^(2^d)
#
# Every coefficient a_i lives in GF(2^m) = F2[x]/(modulus); all
# coefficients of a given instance share one and the same modulus.
# The modulus is assumed irreducible (this is not checked).
#
# Such an L induces an F2-linear map on GF(2^m), regarded as the
# m-dimensional F2-vector space of residue bit strings.
#
# Conventions and caveats:
#
# * Composition.  The natural "product" of two linearized polynomials
#   is composition, (L . M)(x) = L(M(x)), which is again linearized.
#   It is computed here via Frobenius shifts and coefficient
#   arithmetic only.  Ordinary polynomial multiplication is NOT used
#   (a product of two linearized polynomials is in general not even
#   linearized, e.g. x^2 * x = x^3), and this class deliberately does
#   not define a * method.
#
# * Reduction of high Frobenius powers.  Composition is formal:
#   compose() keeps q-degrees unreduced, so exponents i >= m can
#   occur.  Whenever a polynomial is regarded as a MAP on GF(2^m)
#   (evaluate, bit_matrix, kernel, image, roots), the convention is
#   that x^(2^m) = x, i.e. the Frobenius exponent i is identified
#   with i mod m.  functional_normal_form() folds every coefficient
#   a_i into slot (i mod m), producing the unique representative of
#   q-degree < m inducing the same map.
#
# * Zero map vs. zero polynomial.  zero?() means the formal
#   polynomial is zero (all coefficients zero).  A NONZERO formal
#   polynomial can induce the zero map on GF(2^m): the canonical
#   example is x^(2^m) + x.  zero_map?() tests the induced map; by
#   the uniqueness of the reduced representative above, the induced
#   map is zero iff functional_normal_form() is the zero polynomial.
# ================================================================

class F2_lin_poly

	# ------------------------------------------------------------
	# coeffs is an array with coeffs[i] = a_i (coefficient of x^(2^i)).
	# Entries may be Integers, F2_poly's, or F2_poly_mod's with a
	# matching modulus.  Trailing zero coefficients are stripped.
	def initialize(coeffs, modulus)
		if not F2_poly === modulus
			modulus = F2_poly.new(modulus)
		end
		if modulus.degree < 1
			raise "F2_lin_poly:  modulus must have degree >= 1."
		end
		@modulus = modulus
		@m = modulus.degree
		@coeffs = coeffs.collect do |c|
			if F2_poly_mod === c
				if c.modulus != @modulus
					raise "F2_lin_poly:  coefficient modulus mismatch."
				end
				c
			else
				F2_poly_mod.new(c, @modulus)
			end
		end
		while !@coeffs.empty? && @coeffs[-1].zero?
			@coeffs.pop
		end
	end

	attr_reader :modulus, :coeffs

	# ------------------------------------------------------------
	def ==(other)
		F2_lin_poly === other &&
			@modulus == other.modulus &&
			@coeffs == other.coeffs
	end

	# The zero FORMAL polynomial: every coefficient is zero.
	# See zero_map?() for the induced-map analogue.
	def zero?
		@coeffs.empty?
	end

	# The q-degree (Frobenius degree): the largest i with a_i != 0,
	# so the ordinary polynomial degree is 2^q_degree.  The zero
	# polynomial has q-degree -1 by convention.
	def q_degree
		@coeffs.length - 1
	end

	# ------------------------------------------------------------
	def +(other)
		check_modulus(other)
		n = [@coeffs.length, other.coeffs.length].max
		sum = (0...n).collect do |i|
			a = i < @coeffs.length     ? @coeffs[i]       : nil
			b = i < other.coeffs.length ? other.coeffs[i] : nil
			if a.nil?
				b
			elsif b.nil?
				a
			else
				a + b
			end
		end
		F2_lin_poly.new(sum, @modulus)
	end

	# Subtraction is addition in characteristic 2.
	def -(other)
		self + other
	end
	def -@
		F2_lin_poly.new(@coeffs, @modulus)
	end

	# Multiplication by a field scalar (NOT polynomial multiplication).
	def scalar_mul(c)
		c = F2_poly_mod.new(c, @modulus) unless F2_poly_mod === c
		F2_lin_poly.new(@coeffs.collect { |a| a * c }, @modulus)
	end

	# ------------------------------------------------------------
	# The k-fold Frobenius: coefficientwise c -> c^(2^k) (a field
	# automorphism) together with the exponent shift i -> i + k.
	# For k = 1 this is exactly L(x)^2, since in characteristic 2
	#   (sum a_i x^(2^i))^2 = sum a_i^2 x^(2^(i+1)).
	def frobenius(k)
		if k < 0
			raise "F2_lin_poly#frobenius:  negative exponent."
		end
		shifted = Array.new(k) { F2_poly_mod.new(0, @modulus) }
		@coeffs.each do |c|
			fc = c
			k.times { fc = fc * fc }
			shifted.push fc
		end
		F2_lin_poly.new(shifted, @modulus)
	end

	# ------------------------------------------------------------
	# Composition L . M:  (L . M)(x) = L(M(x)) = sum a_i M(x)^(2^i).
	# Built from frobenius() and scalar_mul() only; ordinary
	# polynomial multiplication is never involved.  Exponents are
	# kept formally (q-degrees add); see functional_normal_form()
	# for the map-level reduction.
	def compose(other)
		check_modulus(other)
		rv = F2_lin_poly.new([], @modulus)
		@coeffs.each_with_index do |a, i|
			next if a.zero?
			rv = rv + other.frobenius(i).scalar_mul(a)
		end
		rv
	end

	# ------------------------------------------------------------
	# Evaluation of the induced map at a field element.
	def evaluate(x)
		x = F2_poly_mod.new(x, @modulus) unless F2_poly_mod === x
		sum = F2_poly_mod.new(0, @modulus)
		xp = x # x^(2^0)
		@coeffs.each do |a|
			sum = sum + a * xp
			xp = xp * xp
		end
		sum
	end

	# ------------------------------------------------------------
	# The m x m Bit_matrix of the induced F2-linear map, with the
	# convention that column j holds the coefficient bits of L(x^j)
	# (the image of the j-th standard basis vector), i.e. the matrix
	# acts on column vectors of coefficient bits.  High Frobenius
	# powers are reduced via x^(2^m) = x, as documented above.
	def bit_matrix
		mat = Bit_matrix.new(@m, @m)
		for j in 0..(@m-1)
			ej = F2_poly_mod.new(F2_poly.new(1 << j), @modulus)
			col = evaluate(ej).residue.bits
			for i in 0..(@m-1)
				mat[i][j] = (col >> i) & 1
			end
		end
		mat
	end

	# F2-rank of the induced map (= dimension of the image).
	def rank
		bit_matrix.rank
	end

	# Nullity of the induced map (= log2 of the number of roots).
	def nullity
		@m - rank
	end

	# An F2-basis of the kernel of the induced map, as an array of
	# F2_poly_mod's.  The empty array means the trivial space {0}.
	def kernel
		kb = bit_matrix.kernel_basis
		return [] if kb.nil?
		(0...kb.num_rows).collect do |i|
			F2_poly_mod.new(F2_poly.new(kb.rows[i].bits), @modulus)
		end
	end

	# An F2-basis of the image of the induced map, as an array of
	# F2_poly_mod's.  The empty array means the trivial space {0}.
	def image
		mat = Bit_matrix.new(@m, @m)
		for j in 0..(@m-1)
			ej = F2_poly_mod.new(F2_poly.new(1 << j), @modulus)
			mat.rows[j].bits = evaluate(ej).residue.bits
		end
		mat.row_reduce_below
		basis = []
		for i in 0..(@m-1)
			bits = mat.rows[i].bits
			if bits != 0
				basis.push F2_poly_mod.new(F2_poly.new(bits), @modulus)
			end
		end
		basis
	end

	# All roots of L in GF(2^m), by exhaustive enumeration.  This is
	# O(2^m) and intended for small fields (e.g. testing).
	def roots
		F2_poly_mod.elements_for_modulus(@modulus).select do |x|
			evaluate(x).zero?
		end
	end

	# ------------------------------------------------------------
	# The unique representative of q-degree < m inducing the same
	# F2-linear map on GF(2^m): every coefficient a_i is folded into
	# slot (i mod m), per the convention x^(2^m) = x.  The induced
	# map is the zero map iff this normal form is the zero polynomial.
	def functional_normal_form
		folded = (0...@m).collect { F2_poly_mod.new(0, @modulus) }
		@coeffs.each_with_index do |c, i|
			j = i % @m
			folded[j] = folded[j] + c
		end
		F2_lin_poly.new(folded, @modulus)
	end

	# True iff the induced map on GF(2^m) is identically zero.
	# Note this is WEAKER than zero?(): e.g. x^(2^m) + x is a
	# nonzero formal polynomial inducing the zero map.
	def zero_map?
		functional_normal_form.zero?
	end

	# ------------------------------------------------------------
	# The monic linearized polynomial of q-degree k whose root space
	# is exactly the F2-span of the given elements of GF(2^m)
	# (a "subspace annihilator").  Built recursively: if L vanishes
	# on W and u is a new generator, then
	#
	#   L'(x) = L(x)^2 - L(u) * L(x)
	#
	# vanishes on W + span(u) and is again linearized, since L(x)^2
	# is a Frobenius shift.  Generators already in the root space
	# (i.e. dependent on earlier ones) are skipped, so a spanning
	# set may be passed in place of a basis.
	def F2_lin_poly.annihilator(subspace_basis, modulus)
		if not F2_poly === modulus
			modulus = F2_poly.new(modulus)
		end
		l = F2_lin_poly.new([1], modulus) # The polynomial x.
		subspace_basis.each do |u|
			u = F2_poly_mod.new(u, modulus) unless F2_poly_mod === u
			lu = l.evaluate(u)
			next if lu.zero?
			l = l.frobenius(1) - l.scalar_mul(lu)
		end
		l
	end

	# ------------------------------------------------------------
	def to_s
		terms = []
		@coeffs.each_with_index do |c, i|
			next if c.zero?
			terms << "#{c.residue}*x^(2^#{i})"
		end
		s = terms.empty? ? "0" : terms.join(" + ")
		"[#{s}] mod #{@modulus}"
	end

private
	def check_modulus(other)
		if @modulus != other.modulus
			raise "F2_lin_poly:  modulus mismatch."
		end
	end

end
