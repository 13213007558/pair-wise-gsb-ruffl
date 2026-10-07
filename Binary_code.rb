#!/usr/bin/ruby -Wall

$LOAD_PATH.unshift(File.expand_path(File.dirname(__FILE__)))
require 'Bit_matrix.rb'
require 'Bit_arith.rb'

class Binary_code

	class SearchBudget
		def initialize(limit)
			@limit = limit
			@used = 0
		end
		attr_reader :limit, :used

		def charge(amount = 1)
			return true if @limit.nil?
			@used += amount
			@used <= @limit
		end

		def exhausted?
			!(@limit.nil? || @used < @limit)
		end
	end

	class Result
		def initialize(length:, input_dimension:, rank:, lower_bound:, upper_bound:,
			codeword: nil, information_coefficients: nil,
			reduced_coefficients: nil, basis_coefficients: nil,
			information_sets: 0, budget_used: 0, status: nil)
			@length = length
			@input_dimension = input_dimension
			@rank = rank
			@lower_bound = lower_bound
			@upper_bound = upper_bound
			@codeword = codeword
			@information_coefficients = information_coefficients
			@reduced_coefficients = reduced_coefficients
			@basis_coefficients = basis_coefficients
			@information_sets = information_sets
			@budget_used = budget_used
			@status = status
		end
		attr_reader :length, :input_dimension, :rank, :lower_bound, :upper_bound,
			:codeword, :information_coefficients, :reduced_coefficients,
			:basis_coefficients, :information_sets, :budget_used, :status

		def exact?
			@status == "exact" || @status == "zero-dimensional"
		end

		def minimum_distance
			@status == "zero-dimensional" ? 0 : (exact? ? @upper_bound : nil)
		end

		def to_h
			{
				:length => @length,
				:input_dimension => @input_dimension,
				:rank => @rank,
				:lower_bound => @lower_bound,
				:upper_bound => @upper_bound,
				:minimum_distance => minimum_distance,
				:exact => exact?,
				:codeword => @codeword,
				:information_coefficients => @information_coefficients,
				:reduced_coefficients => @reduced_coefficients,
				:basis_coefficients => @basis_coefficients,
				:information_sets => @information_sets,
				:budget_used => @budget_used,
				:status => @status
			}
		end
	end

	DEFAULT_BUDGET = 2_000_000

	# The generator is not modified.  A witness's information_coefficients
	# always refer to the original input rows, including redundant rows.
	def Binary_code.minimum_distance(generator, positional_budget = nil, budget: nil)
		unless generator.is_a?(Bit_matrix)
			raise ArgumentError, "generator must be a Bit_matrix"
		end
		budget_limit = positional_budget || budget || DEFAULT_BUDGET
		unless budget_limit.nil? || (budget_limit.is_a?(Integer) && budget_limit >= 0)
			raise ArgumentError, "budget must be a non-negative integer or nil"
		end

		length = generator.num_cols
		input_dimension = generator.num_rows
		basis = independent_basis(generator)
		rank = basis[:words].length
		search = SearchBudget.new(budget_limit)

		if rank == 0
			return zero_dimensional_result(length, input_dimension)
		end

		all_columns = (1 << length) - 1
		sets = disjoint_information_sets(basis[:words], all_columns)
		lower_bound = sets.length
		best = basis[:words].each_with_index.map do |word, index|
			[
				Bit_arith.ones(word),
				word,
				1 << index,
				basis[:coefficients][index],
				nil
			]
		end.min_by { |entry| entry[0] }

		if best[0] > lower_bound && !search.exhausted?
			split_search(basis[:words], basis[:coefficients], length,
				lower_bound, best, search)
		end

		complete = best[4] == true
		exact = best[0] <= lower_bound || (!search.exhausted? && complete)
		lower_bound = best[0] if exact
		status = exact ? "exact" : "budget_reached"

		build_result(length, input_dimension, rank, lower_bound, best[0], best[1],
			best[2], best[3], basis[:coefficients], sets.length, search.used, status)
	end

	def Binary_code.independent_basis(generator)
		pivots = {}
		generator.num_rows.times do |row_index|
			word = generator[row_index].bits
			coefficients = 1 << row_index

			while word != 0
				column = Bit_arith.lsb_pos(word)
				if pivots.key?(column)
					pivot = pivots[column]
					word ^= pivot[1]
					coefficients ^= pivot[2]
				else
					pivots[column] = [pivots.length, word, coefficients]
					break
				end
			end
		end

		ordered = pivots.values.sort_by { |entry| entry[0] }
		{
			:words => ordered.map { |entry| entry[1] },
			:coefficients => ordered.map { |entry| entry[2] }
		}
	end

	def Binary_code.disjoint_information_sets(basis, available_columns)
		sets = []
		available = available_columns
		rank = basis.length

		while available != 0
			set = information_set(basis, available, rank)
			break if set == 0
			sets << set
			available &= ~set
		end

		sets
	end

	def Binary_code.information_set(basis, available_columns, rank = basis.length)
		work = basis.dup
		available = available_columns
		selected = 0
		found = 0

		while found < rank
			pivot_row = -1
			pivot_bit = 0

			work.each_with_index do |word, row_index|
				candidate = word & available
				next if candidate == 0
				pivot_row = row_index
				pivot_bit = candidate & -candidate
				break
			end

			break if pivot_row < 0
			pivot_word = work[pivot_row]
			selected |= pivot_bit
			available &= ~pivot_bit
			found += 1

			work[pivot_row] = 0
			work.each_index do |row_index|
				work[row_index] ^= pivot_word if (work[row_index] & pivot_bit) != 0
			end
		end

		found == rank ? selected : 0
	end

	def Binary_code.split_search(basis, basis_maps, length, lower_bound, best, budget)
		rank = basis.length
		right_dimension = rank / 2
		if budget.limit
			while right_dimension > 0 &&
					tree_nodes(right_dimension) > budget.limit / 2
				right_dimension -= 1
			end
		end
		left_dimension = rank - right_dimension

		right_entries, right_complete = enumerate(basis[0, right_dimension], budget)
		root = [nil, nil, nil]
		trie_complete = right_complete

		right_entries.each do |word, coefficients|
			unless insert_trie(root, word, coefficients, length, budget)
				trie_complete = false
				break
			end
		end

		left_entries, left_complete =
			enumerate(basis[right_dimension, left_dimension], budget)
		queried_all = true

		left_entries.each do |word, local_coefficients|
			completed = nearest_trie(root, word, local_coefficients,
				right_dimension, basis_maps, length, best, budget)
			unless completed
				queried_all = false
				break
			end
			return best if best[0] <= lower_bound
		end

		best[4] = trie_complete && left_complete && queried_all &&
			!budget.exhausted?
		best
	end

	def Binary_code.tree_nodes(dimension)
		(1 << (dimension + 1)) - 1
	end

	def Binary_code.enumerate(rows, budget)
		entries = []
		stack = [[0, 0, 0]]
		complete = true

		until stack.empty?
			index, word, coefficients = stack.pop
			unless budget.charge
				complete = false
				break
			end

			if index == rows.length
				entries << [word, coefficients]
			else
				stack << [index + 1, word ^ rows[index], coefficients | (1 << index)]
				stack << [index + 1, word, coefficients]
			end
		end

		[entries, complete]
	end

	def Binary_code.insert_trie(root, word, leaf_coefficients, length, budget)
		node = root
		(length - 1).downto(0) do |position|
			bit = (word >> position) & 1
			node[bit] ||= [nil, nil, nil]
			node = node[bit]
			return false unless budget.charge
		end
		node[2] = [leaf_coefficients, word]
		true
	end

	def Binary_code.nearest_trie(root, left_word, left_local_coefficients,
		left_offset, basis_maps, length, best, budget)
		stack = [[root, 0, 0]]

		until stack.empty?
			node, depth, mismatches = stack.pop
			return false unless budget.charge
			next if mismatches >= best[0]

			if depth == length
				right_coefficients, right_word = node[2]
				reduced = right_coefficients |
					(left_local_coefficients << left_offset)
				next if reduced == 0

				word = left_word ^ right_word
				if mismatches < best[0]
					best[0] = mismatches
					best[1] = word
					best[2] = reduced
					best[3] = original_coefficients(reduced, basis_maps)
				end
				next
			end

			wanted_bit = (left_word >> (length - 1 - depth)) & 1
			opposite = node[1 - wanted_bit]
			preferred = node[wanted_bit]
			stack << [opposite, depth + 1, mismatches + 1] unless opposite.nil?
			stack << [preferred, depth + 1, mismatches] unless preferred.nil?
		end

		true
	end

	def Binary_code.original_coefficients(reduced_coefficients, basis_maps)
		original = 0
		remaining = reduced_coefficients
		while remaining != 0
			index = Bit_arith.lsb_pos(remaining)
			original ^= basis_maps[index]
			remaining &= remaining - 1
		end
		original
	end

	def Binary_code.zero_dimensional_result(length, input_dimension)
		Result.new(
			:length => length,
			:input_dimension => input_dimension,
			:rank => 0,
			:lower_bound => 0,
			:upper_bound => 0,
			:codeword => bit_vector(0, length),
			:information_coefficients => bit_vector(0, input_dimension),
			:reduced_coefficients => [],
			:basis_coefficients => [],
			:information_sets => 0,
			:budget_used => 0,
			:status => "zero-dimensional"
		)
	end

	def Binary_code.build_result(length, input_dimension, rank, lower_bound,
		upper_bound, word, reduced_coefficients, original_coefficients,
		basis_coefficients, information_sets, budget_used, status)
		Result.new(
			:length => length,
			:input_dimension => input_dimension,
			:rank => rank,
			:lower_bound => lower_bound,
			:upper_bound => upper_bound,
			:codeword => bit_vector(word, length),
			:information_coefficients => bit_vector(original_coefficients,
				input_dimension),
			:reduced_coefficients => bit_vector(reduced_coefficients, rank),
			:basis_coefficients => basis_coefficients.map do |coefficients|
				bit_vector(coefficients, input_dimension)
			end,
			:information_sets => information_sets,
			:budget_used => budget_used,
			:status => status
		)
	end

	def Binary_code.bit_vector(bits, length)
		return [] if length == 0
		vector = Bit_vector.new(length)
		vector.bits = bits
		vector
	end

end
