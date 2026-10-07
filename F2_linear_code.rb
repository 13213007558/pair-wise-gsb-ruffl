#!/usr/bin/ruby -Wall

require_relative 'Bit_arith.rb'

class F2_linear_code

	DEFAULT_BUDGET = 1_000_000

	def self.minimum_distance(generator, length = nil, budget = DEFAULT_BUDGET)
		new(generator, length).minimum_distance(budget)
	end

	def self.normalize_generator(generator, supplied_length = nil)
		if defined?(Bit_matrix) && generator.is_a?(Bit_matrix)
			rows = generator.rows.map(&:bits)
			length = generator.num_cols
		elsif generator.is_a?(Array)
			length = supplied_length
			if length.nil?
				length = generator.map do |row|
					if row.is_a?(Array)
						row.length
					elsif defined?(Bit_vector) && row.is_a?(Bit_vector)
						row.num_bits
					elsif row.is_a?(Integer)
						row.bit_length
					else
						raise ArgumentError, "unsupported generator row: #{row.class}"
					end
				end.max || 0
			end

			rows = generator.map.with_index do |row, row_index|
				normalize_row(row, length, row_index)
			end
		elsif defined?(Bit_vector) && generator.is_a?(Bit_vector)
			rows = [generator.bits]
			length = generator.num_bits
		else
			raise ArgumentError, "generator must be an array of binary rows or a Bit_matrix"
		end

		unless length.is_a?(Integer) && length >= 0
			raise ArgumentError, "length must be a non-negative integer"
		end
		[rows, length]
	end

	def self.normalize_row(row, length, row_index)
		if row.is_a?(Integer)
			if row < 0
				raise ArgumentError, "row #{row_index} must not be negative"
			end
			if row.bit_length > length
				raise ArgumentError, "row #{row_index} is longer than #{length}"
			end
			row
		elsif row.is_a?(Array)
			if row.length != length
				raise ArgumentError, "row #{row_index} has length #{row.length}, expected #{length}"
			end
			row.each_with_index.inject(0) do |bits, (bit, column_index)|
				unless bit == 0 || bit == 1
					raise ArgumentError, "entry (#{row_index},#{column_index}) must be 0 or 1"
				end
				bits | (bit << column_index)
			end
		elsif defined?(Bit_vector) && row.is_a?(Bit_vector)
			if row.num_bits != length
				raise ArgumentError, "row #{row_index} has length #{row.num_bits}, expected #{length}"
			end
			row.bits
		else
			raise ArgumentError, "unsupported generator row: #{row.class}"
		end
	end

	def initialize(generator, length = nil)
		input_rows, @length = self.class.normalize_generator(generator, length)
		@input_rows = input_rows
		@num_input_rows = input_rows.length

		@independent_input_rows = []
		@redundant_input_rows = []

		work_rows = input_rows.dup
		work_coefficients = Array.new(@num_input_rows) {|index| 1 << index }
		work_sources = (0...@num_input_rows).to_a
		pivot_by_column = {}
		column = @length - 1
		row = 0

		while row < work_rows.length && column >= 0
			pivot_row = (row...work_rows.length).find {|candidate| work_rows[candidate][column] == 1 }
			if pivot_row.nil?
				column -= 1
				next
			end

			if pivot_row != row
				work_rows[row], work_rows[pivot_row] = work_rows[pivot_row], work_rows[row]
				work_coefficients[row], work_coefficients[pivot_row] =
					work_coefficients[pivot_row], work_coefficients[row]
				work_sources[row], work_sources[pivot_row] =
					work_sources[pivot_row], work_sources[row]
			end

			((row + 1)...work_rows.length).each do |below|
				if work_rows[below][column] == 1
					work_rows[below] ^= work_rows[row]
					work_coefficients[below] ^= work_coefficients[row]
				end
			end

			pivot_by_column[column] = row
			row += 1
			column -= 1
		end

		@rank = row
		@independent_input_rows = work_sources[0...@rank].sort
		@redundant_input_rows = (0...@num_input_rows).to_a - @independent_input_rows
		(@rank...work_rows.length).each do |zero_row|
			raise "Coding error detected" unless work_rows[zero_row] == 0
		end

		pivot_by_column.keys.sort.reverse.each do |pivot_column|
			pivot_row = pivot_by_column[pivot_column]
			(0...pivot_row).each do |above|
				if work_rows[above][pivot_column] == 1
					work_rows[above] ^= work_rows[pivot_row]
					work_coefficients[above] ^= work_coefficients[pivot_row]
				end
			end
		end

		ordered_pivots = pivot_by_column.keys.sort.reverse
		ordered = ordered_pivots.map do |pivot_column|
			pivot_row = pivot_by_column[pivot_column]
			[pivot_column, work_rows[pivot_row], work_coefficients[pivot_row]]
		end

		@pivots = ordered.map {|pivot, _, _| pivot }
		@reduced_basis = ordered.map {|_, row, _| row }
		@reduced_coefficients = ordered.map {|_, _, coefficients| coefficients }
	end

	attr_reader :length, :rank, :num_input_rows, :reduced_basis, :pivots,
		:independent_input_rows, :redundant_input_rows

	def reduced_generator
		@reduced_basis.map {|row| mask_to_bits(row, @length) }
	end

	def reduced_row_original_coefficients
		@reduced_coefficients.map {|mask| mask_to_bits(mask, @num_input_rows) }
	end

	def encode(information)
		mask = information_mask(information)
		if mask.bit_length > @num_input_rows
			raise ArgumentError, "information vector is too long"
		end
		word = 0
		@input_rows.each_with_index do |row, index|
			word ^= row if mask[index] == 1
		end
		mask_to_bits(word, @length)
	end

	def minimum_distance(budget = DEFAULT_BUDGET)
		unless budget.nil? || (budget.is_a?(Integer) && budget >= 0)
			raise ArgumentError, "budget must be nil or a non-negative integer"
		end

		if @rank == 0
			return result(0, 0, 0, 0, true, 0, false)
		end

		index = (0...@rank).min_by {|i| Bit_arith.ones(@reduced_basis[i]) }
		upper = Bit_arith.ones(@reduced_basis[index])
		witness_reduced = 1 << index
		witness_original = @reduced_coefficients[index]
		lower = 1
		operations = 0
		stopped = false

		if upper > 1
			lower = 2
		end

		if lower == upper
			return result(lower, upper, witness_reduced, witness_original, true, operations, false)
		end

		right_count = @rank / 2
		left_count = @rank - right_count
		trie = [nil, nil, nil]

		if right_count > 0
			word = 0
			coefficients = 0
			count = 1 << right_count
			(0...count).each do |combination|
				if combination > 0
					changed = (combination & -combination).bit_length - 1
					word ^= @reduced_basis[left_count + changed]
					coefficients ^= 1 << (left_count + changed)
				end

				if word != 0 && Bit_arith.ones(word) < upper
					upper = Bit_arith.ones(word)
					witness_reduced = coefficients
					witness_original = reduced_to_original(coefficients)
				end

				_, operations, stopped = insert_trie(trie, word, @length, coefficients, operations, budget)
				if upper == lower
					return result(lower, upper, witness_reduced, witness_original, true, operations, false)
				end
				if stopped
					return result(lower, upper, witness_reduced, witness_original, false, operations, true)
				end
			end
		end

		word = 0
		coefficients = 0
		count = 1 << left_count
		(1...count).each do |combination|
			changed = (combination & -combination).bit_length - 1
			word ^= @reduced_basis[changed]
			coefficients ^= 1 << changed

			distance, right_coefficients, operations, stopped = nearest_trie(
				trie, word, @length, upper, operations, budget
			)
			unless distance.nil?
				combined = coefficients ^ right_coefficients
				if distance < upper
					upper = distance
					witness_reduced = combined
					witness_original = reduced_to_original(combined)
				end
			end
			if stopped
				return result(lower, upper, witness_reduced, witness_original, false, operations, true)
			end

			if upper == lower
				return result(lower, upper, witness_reduced, witness_original, true, operations, false)
			end
		end

		result(upper, upper, witness_reduced, witness_original, true, operations, false)
	end

	private

	def information_mask(information)
		if information.is_a?(Array)
			if information.length != @num_input_rows
				raise ArgumentError, "expected #{@num_input_rows} information bits"
			end
			information.each_with_index.inject(0) do |mask, (bit, index)|
				unless bit == 0 || bit == 1
					raise ArgumentError, "information bit #{index} must be 0 or 1"
				end
				mask | (bit << index)
			end
		elsif information.is_a?(Integer)
			if information < 0
				raise ArgumentError, "information mask must not be negative"
			end
			information
		else
			raise ArgumentError, "information must be an array or integer mask"
		end
	end

	def reduced_to_original(mask)
		original = 0
		(0...@rank).each do |index|
			original ^= @reduced_coefficients[index] if mask[index] == 1
		end
		original
	end

	def insert_trie(root, word, length, terminal_mask, operations, budget)
		node = root
		(length - 1).downto(0) do |column|
			operations += 1
			if !budget.nil? && operations > budget
				return [false, operations, true]
			end

			bit = word[column]
			if node[bit].nil?
				node[bit] = [nil, nil, nil]
			end
			node = node[bit]
		end
		node[2] = terminal_mask
		[true, operations, false]
	end

	def nearest_trie(root, target, length, upper_bound, operations, budget)
		stack = [[root, length - 1, 0]]
		best_distance = upper_bound
		best_mask = nil
		until stack.empty?
			node, column, distance = stack.pop
			operations += 1
			if !budget.nil? && operations > budget
				if best_mask.nil?
					return [nil, nil, operations, true]
				else
					return [best_distance, best_mask, operations, true]
				end
			end

			next if distance >= best_distance

			if column < 0
				best_distance = distance
				best_mask = node[2]
				next
			end

			target_bit = target[column]
			other_bit = target_bit ^ 1
			if node[other_bit]
				stack << [node[other_bit], column - 1, distance + 1]
			end
			if node[target_bit]
				stack << [node[target_bit], column - 1, distance]
			end
		end

		if best_mask.nil?
			[nil, nil, operations, false]
		else
			[best_distance, best_mask, operations, false]
		end
	end

	def result(lower, upper, reduced_mask, original_mask, exact, operations, stopped)
		word = 0
		(0...@rank).each do |index|
			word ^= @reduced_basis[index] if reduced_mask[index] == 1
		end

		{
			length: @length,
			input_dimension: @num_input_rows,
			dimension: @rank,
			rank: @rank,
			minimum_distance: exact ? lower : nil,
			lower_bound: lower,
			upper_bound: upper,
			exact: exact,
			budget_exhausted: stopped,
			nodes_searched: operations,
			codeword: mask_to_bits(word, @length),
			codeword_mask: word,
			codeword_weight: Bit_arith.ones(word),
			nonzero_codeword: word != 0,
			information_coefficients: mask_to_bits(original_mask, @num_input_rows),
			information_mask: original_mask,
			reduced_information_coefficients: mask_to_bits(reduced_mask, @rank),
			reduced_information_mask: reduced_mask,
			reduced_generator: reduced_generator,
			reduced_row_original_coefficients: reduced_row_original_coefficients,
			independent_input_rows: @independent_input_rows.dup,
			redundant_input_rows: @redundant_input_rows.dup,
			zero_columns: zero_columns
		}
	end

	def zero_columns
		occupied = 0
		@reduced_basis.each {|row| occupied |= row }
		(0...@length).select {|column| occupied[column] == 0 }
	end

	def mask_to_bits(mask, length)
		Array.new(length) {|column| mask[column] }
	end
end
