#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# ================================================================

require_relative 'F2_poly_mod_linearized.rb'
require 'test/unit'

class F2_poly_mod_linearized_unit_test < Test::Unit::TestCase

	def test_coefficientwise_addition_keeps_formal_indices
		modulus = F2_poly.new(0xb)
		a = F2_poly_mod_linearized.new(
			[F2_poly_mod.new(1, modulus), F2_poly_mod.new(2, modulus)],
			modulus)
		b = F2_poly_mod_linearized.new({
			1 => F2_poly_mod.new(3, modulus),
			3 => F2_poly_mod.new(1, modulus)
		}, modulus)

		expected = F2_poly_mod_linearized.new({
			0 => F2_poly_mod.new(1, modulus),
			1 => F2_poly_mod.new(1, modulus),
			3 => F2_poly_mod.new(1, modulus)
		}, modulus)
		assert_equal(expected, a + b)
		assert_equal(true, (a + a).zero?)
		assert_equal(a + b, a - b)
		assert_equal(a + b, -a + b)
	end

	def test_composition_uses_frobenius_twisting
		modulus = F2_poly.new(0xb)
		one = F2_poly_mod.new(1, modulus)
		a = F2_poly_mod_linearized.new([one, one], modulus)
		b = F2_poly_mod_linearized.new(
			[one, F2_poly_mod.new(3, modulus)], modulus)

		# A = X + X^2, B = X + alpha X^2.
		# A o B = X + (alpha + 1) X^2 + alpha^2 X^4.
		expected = F2_poly_mod_linearized.new({
			0 => one,
			1 => F2_poly_mod.new(2, modulus),
			2 => F2_poly_mod.new(5, modulus)
		}, modulus)
		assert_equal(expected, a.compose(b))
		assert_equal(expected, a * b)
		assert_equal(true, a.compose(b)[3].zero?)
	end

	def test_high_formal_indices_are_reduced_only_for_the_field_map
		modulus = F2_poly.new(0xb)
		one = F2_poly_mod.new(1, modulus)
		field_polynomial = F2_poly_mod_linearized.field_polynomial(modulus)
		b = F2_poly_mod_linearized.new(
			[one, F2_poly_mod.new(3, modulus)], modulus)

		assert_equal(3, field_polynomial.q_degree)
		assert_equal(false, field_polynomial.reduced?)
		assert_equal(false, field_polynomial.zero?)
		assert_equal(true, field_polynomial.zero_map?)
		assert_equal(true, field_polynomial.reduced_form.zero?)

		formal_composition = field_polynomial.compose(b)
		expected_formal = F2_poly_mod_linearized.new({
			0 => one,
			1 => F2_poly_mod.new(3, modulus),
			3 => one,
			4 => F2_poly_mod.new(3, modulus)
		}, modulus)
		assert_equal(expected_formal, formal_composition)
		assert_equal(true, field_polynomial.compose(b, true).zero?)
		assert_equal(true, field_polynomial.compose(b).zero_map?)

		F2_poly_mod.elements_for_modulus(modulus).each do |element|
			assert_equal(F2_poly_mod.new(0, modulus), field_polynomial.evaluate(element))
		end
	end

	def test_zero_formal_polynomial_and_zero_map
		modulus = F2_poly.new(0xb)
		zero = F2_poly_mod_linearized.zero(modulus)
		field_polynomial = F2_poly_mod_linearized.field_polynomial(modulus)

		assert_equal(true, zero.zero?)
		assert_equal(true, zero.zero_map?)
		assert_equal(0, zero.bit_matrix.rank)
		assert_equal(3, zero.kernel_dimension)
		assert_equal(0, zero.image_dimension)

		assert_equal(false, field_polynomial.zero?)
		assert_equal(true, field_polynomial.zero_map?)
		assert_equal(true, (field_polynomial + field_polynomial).zero?)
	end

	def test_exhaustive_small_field_roots_and_bit_matrix_dimensions
		[0x3, 0x7, 0xb].each do |modulus_bits|
			modulus = F2_poly.new(modulus_bits)
			n = modulus.degree
			field_size = 1 << n
			elements = F2_poly_mod.elements_for_modulus(modulus)

			(0...(field_size ** n)).each do |mask|
				coefficients = (0...n).collect do |index|
					bits = (mask >> (index * n)) & (field_size - 1)
					F2_poly_mod.new(bits, modulus)
				end
				linear_map = F2_poly_mod_linearized.new(coefficients, modulus)
				matrix = linear_map.bit_matrix
				kernel_dimension = n - matrix.rank
				image_dimension = matrix.rank

				assert_equal(kernel_dimension, linear_map.kernel_dimension)
				assert_equal(image_dimension, linear_map.image_dimension)

				roots = elements.select do |element|
					linear_map.evaluate(element).zero?
				end
				assert_equal(1 << kernel_dimension, roots.length)
				assert_equal(span_bits(linear_map.kernel_basis),
					roots.collect {|element| element.residue.bits}.sort)

				images = elements.collect do |element|
					linear_map.evaluate(element).residue.bits
				end.uniq.sort
				assert_equal(1 << image_dimension, images.length)
				assert_equal(span_bits(linear_map.image_basis), images)
			end
		end
	end

	def test_subspace_annihilators_on_every_small_subset
		[0x3, 0x7, 0xb].each do |modulus_bits|
			modulus = F2_poly.new(modulus_bits)
			n = modulus.degree
			elements = F2_poly_mod.elements_for_modulus(modulus)
			nonzero_elements = elements.reject {|element| element.zero?}

		assert_equal(F2_poly_mod_linearized.x(modulus),
			F2_poly_mod_linearized.from_subspace_basis([], modulus))

		(0..n).each do |subset_size|
			nonzero_elements.combination(subset_size).each do |subset|
			if subset_size > 0
				basis_matrix = Bit_matrix.new(subset_size, n)
				subset.each_with_index do |element, row|
					basis_matrix[row].bits = element.residue.bits
				end
			end

				if subset.length > 0 && basis_matrix.rank != subset.length
					assert_raise(RuntimeError) do
						F2_poly_mod_linearized.from_subspace_basis(subset)
					end
					next
				end

				annihilator = if subset.empty?
					F2_poly_mod_linearized.from_subspace_basis(subset, modulus)
				else
					F2_poly_mod_linearized.from_subspace_basis(subset)
				end
				assert_equal(subset.length, annihilator.kernel_dimension)
				assert_equal(span_bits(subset),
					elements.select {|element| annihilator.evaluate(element).zero?}
						.collect {|element| element.residue.bits}.sort)
			end
		end
		end
	end

	def test_full_basis_annihilator_is_nonzero_formal_zero_map
		modulus = F2_poly.new(0xb)
		basis = [1, 2, 4].collect {|bits| F2_poly_mod.new(bits, modulus)}
		annihilator = F2_poly_mod_linearized.from_subspace_basis(basis)

		assert_equal(F2_poly_mod_linearized.field_polynomial(modulus), annihilator)
		assert_equal(false, annihilator.zero?)
		assert_equal(true, annihilator.zero_map?)
	end

	def test_rejects_reducible_modulus_and_mixed_fields
		assert_raise(RuntimeError) do
			F2_poly_mod_linearized.new([1], 0x5)
		end

		first = F2_poly_mod_linearized.new([F2_poly_mod.new(1, 0xb)], 0xb)
		second = F2_poly_mod_linearized.new([F2_poly_mod.new(1, 0x7)], 0x7)
		assert_raise(RuntimeError) {first + second}
		assert_raise(RuntimeError) {first.compose(second)}
	end

	private

	def span_bits(elements)
		bits = elements.collect {|element| element.residue.bits}
		span = [0]
		bits.each do |bit|
			span.concat(span.collect {|existing| existing ^ bit})
		end
		span.uniq.sort
	end
end
