#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# ================================================================

require 'F2_lin_poly.rb'
require 'test/unit'

class F2_lin_poly_unit_test < Test::Unit::TestCase

	# Irreducible moduli: x^2+x+1, x^3+x+1, x^4+x+1, x^6+x+1.
	def setup
		@mod2 = F2_poly.new(0b111)
		@mod3 = F2_poly.new(0b1011)
		@mod4 = F2_poly.new(0b10011)
		@mod6 = F2_poly.new(0b1000011)
	end

	# ----------------------------------------------------------------
	# Helpers

	def random_lin_poly(modulus, max_qdeg)
		m = modulus.degree
		n = rand(0..(max_qdeg + 1))
		coeffs = (0...n).collect { F2_poly.new(rand(1 << m)) }
		F2_lin_poly.new(coeffs, modulus)
	end

	def elements_of(modulus)
		F2_poly_mod.elements_for_modulus(modulus)
	end

	def span_of(basis_elements, modulus)
		k = basis_elements.length
		elts = []
		(0...(1 << k)).each do |mask|
			acc = F2_poly_mod.new(0, modulus)
			k.times do |i|
				acc = acc + basis_elements[i] if ((mask >> i) & 1) == 1
			end
			elts.push acc
		end
		elts
	end

	def power_of_two?(n)
		n > 0 && (n & (n - 1)) == 0
	end

	# ----------------------------------------------------------------
	def test_basics
		zero = F2_lin_poly.new([], @mod4)
		assert_true(zero.zero?)
		assert_equal(-1, zero.q_degree)
		assert_false(F2_lin_poly.new([0, 1], @mod4).zero?)

		# Trailing zero coefficients are stripped.
		l = F2_lin_poly.new([1, 0, 0], @mod4)
		assert_equal(0, l.q_degree)
		assert_equal(F2_lin_poly.new([1], @mod4), l)

		# Coefficient modulus mismatch is rejected.
		assert_raise(RuntimeError) do
			F2_lin_poly.new([F2_poly_mod.new(1, @mod3)], @mod4)
		end
		assert_raise(RuntimeError) do
			F2_lin_poly.new([1], @mod3) + F2_lin_poly.new([1], @mod4)
		end
	end

	def test_addition
		srand(4242)
		[@mod2, @mod3, @mod4].each do |modulus|
			10.times do
				l = random_lin_poly(modulus, 3)
				m = random_lin_poly(modulus, 3)
				sum = l + m
				elements_of(modulus).each do |x|
					assert_equal(l.evaluate(x) + m.evaluate(x), sum.evaluate(x))
				end
				# Pointwise check against coefficientwise xor.
				n = [l.coeffs.length, m.coeffs.length].max
				(0...n).each do |i|
					a = i < l.coeffs.length ? l.coeffs[i] : F2_poly_mod.new(0, modulus)
					b = i < m.coeffs.length ? m.coeffs[i] : F2_poly_mod.new(0, modulus)
					s = i < sum.coeffs.length ? sum.coeffs[i] : F2_poly_mod.new(0, modulus)
					assert_equal(a + b, s)
				end
			end
		end
	end

	def test_frobenius
		srand(7)
		[@mod2, @mod3, @mod4].each do |modulus|
			10.times do
				l = random_lin_poly(modulus, 3)
				sq = l.frobenius(1)
				# Coefficientwise: a_i^2 shifted up by one slot.
				assert_equal(l.q_degree + 1, sq.q_degree) unless l.zero?
				l.coeffs.each_with_index do |c, i|
					assert_equal(c * c, sq.coeffs[i + 1])
				end
				# Map-level: frobenius(1) is pointwise squaring.
				elements_of(modulus).each do |x|
					lx = l.evaluate(x)
					assert_equal(lx * lx, sq.evaluate(x))
				end
			end
		end
	end

	def test_compose
		# Hand-computed examples over GF(4), modulus x^2+x+1.
		x   = F2_lin_poly.new([1], @mod2)    # x
		sq = F2_lin_poly.new([0, 1], @mod2) # x^2

		# (x^2) . (x) = x^2, whereas ordinary multiplication would
		# give x^3 (not even linearized).  Compose is not multiply.
		assert_equal(sq, sq.compose(x))

		# (x^2) . (x^2) = x^4, kept formally (q-degree 2 > m - 1).
		x4 = sq.compose(sq)
		assert_equal(F2_lin_poly.new([0, 0, 1], @mod2), x4)

		# L = x^2 + x, M = x^2 + x over GF(4):
		# L . M = M^2 + M = (x^4 + x^2) + (x^2 + x) = x^4 + x.
		l = F2_lin_poly.new([1, 1], @mod2)
		assert_equal(F2_lin_poly.new([1, 0, 1], @mod2), l.compose(l))

		# Random round-trip through evaluation, with coefficients
		# from the extension field.
		srand(31337)
		[@mod2, @mod3, @mod4].each do |modulus|
			10.times do
				a = random_lin_poly(modulus, 2)
				b = random_lin_poly(modulus, 2)
				ab = a.compose(b)
				elements_of(modulus).each do |v|
					assert_equal(a.evaluate(b.evaluate(v)), ab.evaluate(v))
				end
			end
		end
	end

	def test_functional_normal_form_and_zero_map
		# Over GF(2^3): x^(2^3) + x is a NONZERO formal polynomial
		# inducing the ZERO map.
		l = F2_lin_poly.new([1, 0, 0, 1], @mod3)
		assert_false(l.zero?)
		assert_true(l.zero_map?)
		assert_equal(F2_lin_poly.new([], @mod3), l.functional_normal_form)
		elements_of(@mod3).each do |v|
			assert_true(l.evaluate(v).zero?)
		end

		# x^(2^4) over GF(2^3): exponent 4 == 1 (mod 3), so the
		# normal form is x^2.
		l = F2_lin_poly.new([0, 0, 0, 0, 1], @mod3)
		assert_equal(F2_lin_poly.new([0, 1], @mod3), l.functional_normal_form)
		assert_false(l.zero_map?)

		# x^(2^2) over GF(2^2) reduces to the identity map x.
		l = F2_lin_poly.new([0, 0, 1], @mod2)
		assert_equal(F2_lin_poly.new([1], @mod2), l.functional_normal_form)

		# The identity map is not the zero map.
		assert_false(F2_lin_poly.new([0, 1], @mod3).zero_map?)

		# Random high-q-degree polynomials: normal form induces the
		# same map and has q-degree < m.
		srand(2718)
		[@mod2, @mod3, @mod4].each do |modulus|
			10.times do
				l = random_lin_poly(modulus, modulus.degree + 3)
				nf = l.functional_normal_form
				assert_true(nf.q_degree < modulus.degree)
				elements_of(modulus).each do |v|
					assert_equal(l.evaluate(v), nf.evaluate(v))
				end
			end
		end
	end

	def test_kernel_and_image
		srand(161)
		[@mod2, @mod3, @mod4, @mod6].each do |modulus|
			m = modulus.degree
			8.times do
				# Include exponents >= m to exercise the reduction
				# convention as well.
				l = random_lin_poly(modulus, m + 2)

				# Brute-force root space over the small field.
				roots = l.roots
				assert_true(power_of_two?(roots.length))

				# Kernel basis: elements are roots, and it spans
				# exactly the root space.
				kb = l.kernel
				assert_equal(roots.length, 1 << kb.length)
				kb.each { |u| assert_true(l.evaluate(u).zero?) }
				span_of(kb, modulus).each do |u|
					assert_true(l.evaluate(u).zero?)
				end

				# Dimension cross-check against the bit matrix.
				assert_equal(m, l.bit_matrix.rank + kb.length)
				assert_equal(kb.length, l.nullity)

				# Image basis: spans exactly the set of values.
				ib = l.image
				assert_equal(l.bit_matrix.rank, ib.length)
				assert_equal(m, ib.length + kb.length)
				values = elements_of(modulus).collect { |v| l.evaluate(v).residue.bits }.uniq
				assert_equal(values.length, 1 << ib.length)
				span_of(ib, modulus).each do |v|
					assert_true(values.include?(v.residue.bits))
				end
			end
		end
	end

	def test_annihilator
		srand(555)
		[@mod2, @mod3, @mod4, @mod6].each do |modulus|
			m = modulus.degree
			6.times do
				# Random subspace via an independent random basis.
				k = rand(0..m)
				basis = []
				while basis.length < k
					u = F2_poly_mod.new(F2_poly.new(rand(1 << m)), modulus)
					next if span_of(basis, modulus).include?(u)
					basis.push u
				end

				l = F2_lin_poly.annihilator(basis, modulus)

				# Monic of q-degree k.
				assert_equal(k, l.q_degree)
				assert_true(l.coeffs[k].one?)

				# Vanishes on the subspace ...
				span_of(basis, modulus).each do |u|
					assert_true(l.evaluate(u).zero?)
				end

				# ... and nowhere else: the root space is exactly
				# the subspace.
				assert_equal(1 << k, l.roots.length)
			end
		end

		# The empty subspace is annihilated by x.
		assert_equal(F2_lin_poly.new([1], @mod4),
			F2_lin_poly.annihilator([], @mod4))

		# The full space GF(2^m) is annihilated by x^(2^m) + x.
		# (Check the induced map, since annihilator() keeps formal
		# q-degree m.)
		full_basis = (0...@mod4.degree).collect do |j|
			F2_poly_mod.new(F2_poly.new(1 << j), @mod4)
		end
		l = F2_lin_poly.annihilator(full_basis, @mod4)
		assert_equal(@mod4.degree, l.q_degree)
		assert_true(l.zero_map?)
	end

	def test_zero_polynomial_map
		zero = F2_lin_poly.new([], @mod4)
		assert_true(zero.zero?)
		assert_true(zero.zero_map?)
		elements_of(@mod4).each do |v|
			assert_true(zero.evaluate(v).zero?)
		end
		# Kernel of the zero map is the whole space.
		assert_equal(@mod4.degree, zero.kernel.length)
		assert_equal(0, zero.bit_matrix.rank)
		assert_equal(0, zero.image.length)
	end

end
