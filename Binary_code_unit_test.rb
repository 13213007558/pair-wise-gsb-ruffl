#!/usr/bin/ruby -Wall

require_relative 'Binary_code.rb'
require 'test/unit'

class Binary_codeUnitTest < Test::Unit::TestCase

	def matrix(rows)
		g = Bit_matrix.new(rows.length, rows.first.length)
		rows.each_with_index do |text, row_index|
			text.each_char.with_index do |char, column_index|
				g[row_index][rows.first.length - 1 - column_index] = char.to_i
			end
		end
		g
	end

	def test_redundant_generator_preserves_original_coefficients
		g = matrix([
			"1100",
			"0110",
			"1010",
			"0000"
		])

		result = Binary_code.minimum_distance(g, nil)

		assert_equal(2, result.rank)
		assert_equal(2, result.minimum_distance)
		assert_equal("1100", result.codeword.to_s)
		assert_equal(1, result.information_coefficients[0])
		assert_equal(1, result.reduced_coefficients[0])
		assert_equal(2, result.basis_coefficients.length)
	end

	def test_dependent_row_combination_is_returned_with_original_vector
		g = matrix([
			"0110",
			"1100",
			"1010"
		])

		result = Binary_code.minimum_distance(g, nil)

		assert_equal(2, result.minimum_distance)
		assert_equal(2, Bit_arith.ones(result.codeword.bits))
		assert_equal(result.codeword.bits,
			encode(g, result.information_coefficients.bits))
		assert_equal(1, Bit_arith.ones(result.information_coefficients.bits))
	end

	def test_witness_can_combine_independent_and_redundant_input_rows
		g = matrix([
			"0111",
			"0110",
			"0111",
			"0000"
		])

		result = Binary_code.minimum_distance(g, nil)

		assert_equal(2, result.rank)
		assert_equal(1, result.minimum_distance)
		assert_equal("0001", result.codeword.to_s)
		assert_equal(3, result.information_coefficients.bits)
		assert_equal(result.codeword.bits,
			encode(g, result.information_coefficients.bits))
	end

	def test_zero_columns_are_kept_and_counted_in_weight
		g = matrix([
			"1000",
			"0001"
		])

		result = Binary_code.minimum_distance(g, nil)

		assert_equal(4, result.length)
		assert_equal(1, result.minimum_distance)
		assert_equal(result.codeword.bits,
			encode(g, result.information_coefficients.bits))
	end

	def test_zero_dimensional_code
		g = matrix([
			"0000",
			"0000"
		])

		result = Binary_code.minimum_distance(g, nil)

		assert_equal(0, result.rank)
		assert(result.exact?)
		assert_equal(0, result.lower_bound)
		assert_equal(0, result.upper_bound)
		assert_equal(0, result.minimum_distance)
		assert_equal("0000", result.codeword.to_s)
		assert_equal("00", result.information_coefficients.to_s)
	end

	def test_repetition_code_uses_information_set_certificate
		g = matrix([
			"1111",
			"1111",
			"0000"
		])

		result = Binary_code.minimum_distance(g, 0)

		assert_equal(4, result.lower_bound)
		assert_equal(4, result.upper_bound)
		assert_equal(4, result.minimum_distance)
		assert_equal(1, result.information_coefficients[0])
	end

	def test_budget_stop_returns_bounds_and_witness
		rows = []
		18.times do |row_index|
			row = "0" * 40
			[row_index, row_index + 1, row_index + 2].each do |column|
				row[column % 40] = "1"
			end
			rows << row
		end
		g = matrix(rows)

		result = Binary_code.minimum_distance(g, 10)

		assert_equal(18, result.rank)
		assert(!result.exact?)
		assert(result.lower_bound <= result.upper_bound)
		assert(result.lower_bound >= 1)
		assert(result.upper_bound <= 40)
		assert_equal(result.codeword.bits,
			encode(g, result.information_coefficients.bits))
		assert_equal("budget_reached", result.status)
	end

	def test_row_reordering_does_not_change_distance
		a = matrix(["111000", "000111", "111111"])
		b = matrix(["111111", "000111", "111000"])

		ra = Binary_code.minimum_distance(a, nil)
		rb = Binary_code.minimum_distance(b, nil)

		assert_equal(3, ra.minimum_distance)
		assert_equal(ra.minimum_distance, rb.minimum_distance)
		assert_equal(ra.codeword.bits,
			encode(a, ra.information_coefficients.bits))
		assert_equal(rb.codeword.bits,
			encode(b, rb.information_coefficients.bits))
	end

	def encode(generator, coefficients)
		word = 0
		generator.num_rows.times do |row_index|
			word ^= generator[row_index].bits if ((coefficients >> row_index) & 1) != 0
		end
		word
	end
end
