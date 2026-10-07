#!/usr/bin/ruby -Wall

require_relative 'F2_linear_code.rb'
require_relative 'Bit_matrix.rb'
require 'test/unit'

class F2_linear_code_unit_test < Test::Unit::TestCase

	def test_simplex_code_exact_distance_and_original_information
		generator = [
			[1, 0, 0, 1, 1, 0, 1],
			[0, 1, 0, 1, 0, 1, 1],
			[0, 0, 1, 0, 1, 1, 1]
		]
		result = F2_linear_code.minimum_distance(generator, 7, nil)

		assert_equal(7, result[:length])
		assert_equal(3, result[:dimension])
		assert_equal(4, result[:minimum_distance])
		assert_equal(4, result[:lower_bound])
		assert_equal(4, result[:upper_bound])
		assert_equal(true, result[:exact])
		assert_equal(4, result[:codeword_weight])
		assert_equal(true, result[:nonzero_codeword])

		code = F2_linear_code.new(generator, 7)
		assert_equal(result[:codeword], code.encode(result[:information_coefficients]))
		assert_equal(4, result[:codeword].count(1))
		assert_operator(result[:nodes_searched], :>, 0)
	end

	def test_redundant_rows_preserve_original_coefficient_mapping
		generator = [
			[1, 1, 0, 0],
			[0, 1, 1, 0],
			[1, 0, 1, 0],
			[0, 0, 0, 0]
		]
		result = F2_linear_code.minimum_distance(generator, 4, nil)
		code = F2_linear_code.new(generator, 4)

		assert_equal(2, result[:dimension])
		assert_equal(2, result[:minimum_distance])
		assert_equal([0, 1], result[:independent_input_rows])
		assert_equal([2, 3], result[:redundant_input_rows])
		assert_equal(result[:codeword], code.encode(result[:information_coefficients]))
		assert_equal(2, result[:codeword_weight])

		assert_equal(2, result[:reduced_generator].length)
		assert_equal(result[:reduced_generator].length,
			result[:reduced_row_original_coefficients].length)

		result[:reduced_generator].each_with_index do |_, index|
			original = result[:reduced_row_original_coefficients][index]
			assert_equal(result[:reduced_generator][index], code.encode(original))
		end
	end

	def test_row_reordering_and_duplicate_rows
		generator = [
			[0, 0, 0, 1],
			[1, 1, 0, 0],
			[0, 0, 0, 1],
			[1, 1, 0, 0]
		]
		result = F2_linear_code.minimum_distance(generator, 4, nil)

		assert_equal(2, result[:dimension])
		assert_equal(1, result[:minimum_distance])
		assert_equal(true, result[:exact])
		assert_equal([0, 1], result[:independent_input_rows])
		assert_equal([2, 3], result[:redundant_input_rows])
		assert_equal(1, result[:codeword_weight])
		assert_equal(result[:codeword], F2_linear_code.new(generator, 4)
			.encode(result[:information_coefficients]))
	end

	def test_zero_columns_are_reported_without_changing_distance
		generator = [[1, 1, 1, 0]]
		result = F2_linear_code.minimum_distance(generator, 4, nil)

		assert_equal(3, result[:minimum_distance])
		assert_equal([3], result[:zero_columns])
		assert_equal(3, result[:codeword_weight])
		assert_equal(result[:codeword], F2_linear_code.new(generator, 4)
			.encode(result[:information_coefficients]))
	end

	def test_zero_dimensional_nonempty_code
		result = F2_linear_code.minimum_distance([[0, 0, 0], [0, 0, 0]], 3, nil)

		assert_equal(0, result[:minimum_distance])
		assert_equal(0, result[:lower_bound])
		assert_equal(0, result[:upper_bound])
		assert_equal(true, result[:exact])
		assert_equal(0, result[:dimension])
		assert_equal([0, 0, 0], result[:codeword])
		assert_equal([0, 0], result[:information_coefficients])
		assert_equal([], result[:reduced_generator])
		assert_equal([0, 1], result[:redundant_input_rows])
		assert_equal([0, 1, 2], result[:zero_columns])
		assert_equal(false, result[:nonzero_codeword])
	end

	def test_zero_dimensional_zero_length_code
		result = F2_linear_code.minimum_distance([], 0, nil)

		assert_equal(0, result[:minimum_distance])
		assert_equal(0, result[:length])
		assert_equal(0, result[:dimension])
		assert_equal([], result[:codeword])
		assert_equal([], result[:information_coefficients])
		assert_equal([], result[:zero_columns])
		assert_equal(true, result[:exact])
	end

	def test_zero_length_nonzero_number_of_zero_rows
		result = F2_linear_code.minimum_distance([], 0, nil)
		code = F2_linear_code.new(Array.new(2) { [] }, 0)
		explicit = code.minimum_distance(nil)

		assert_equal(0, result[:minimum_distance])
		assert_equal(2, explicit[:input_dimension])
		assert_equal(0, explicit[:dimension])
		assert_equal([], explicit[:codeword])
		assert_equal([0, 1], explicit[:redundant_input_rows])
		assert_equal(true, explicit[:exact])
	end

	def test_budget_can_stop_with_bounds_and_valid_witness
		generator = [
			[1, 0, 0, 1, 1, 0, 1],
			[0, 1, 0, 1, 0, 1, 1],
			[0, 0, 1, 0, 1, 1, 1]
		]
		result = F2_linear_code.minimum_distance(generator, 7, 0)

		assert_nil(result[:minimum_distance])
		assert_equal(false, result[:exact])
		assert_equal(true, result[:budget_exhausted])
		assert_equal(2, result[:lower_bound])
		assert_equal(4, result[:upper_bound])
		assert_operator(result[:lower_bound], :<=, result[:upper_bound])
		assert_equal(result[:upper_bound], result[:codeword_weight])
		assert_equal(result[:codeword], F2_linear_code.new(generator, 7)
			.encode(result[:information_coefficients]))
	end

	def test_proven_lower_bound_is_exact_even_with_zero_budget
		generator = [[1, 1, 0, 0], [1, 0, 1, 0]]
		result = F2_linear_code.minimum_distance(generator, 4, 0)

		assert_equal(2, result[:minimum_distance])
		assert_equal(true, result[:exact])
		assert_equal(false, result[:budget_exhausted])
		assert_equal(2, result[:lower_bound])
		assert_equal(2, result[:upper_bound])
	end

	def test_integer_rows_use_coordinate_zero_as_rightmost_bit
		result = F2_linear_code.minimum_distance([0b101, 0b011], 3, nil)

		assert_equal(2, result[:minimum_distance])
		assert_equal(true, result[:exact])
		assert_equal(result[:codeword], F2_linear_code.new([0b101, 0b011], 3)
			.encode(result[:information_mask]))
	end

	def test_accepts_bit_matrix_and_reports_original_row_coefficients
		matrix = Bit_matrix.new(2, 3)
		matrix[0][0] = 1
		matrix[0][2] = 1
		matrix[1][1] = 1
		matrix[1][2] = 1

		result = F2_linear_code.minimum_distance(matrix, nil, nil)

		assert_equal(3, result[:length])
		assert_equal(2, result[:dimension])
		assert_equal(2, result[:minimum_distance])
		assert_equal(true, result[:exact])
		assert_equal(result[:codeword], F2_linear_code.new(matrix)
			.encode(result[:information_mask]))
	end
end
