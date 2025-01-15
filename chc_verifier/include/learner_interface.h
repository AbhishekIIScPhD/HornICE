/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef __CHCTEACHER_LEARNER_INTERFACE_H__
#define __CHCTEACHER_LEARNER_INTERFACE_H__

// C++ includes
#include <list>
#include <stdexcept>
#include <vector>
#include <iostream>
#include <algorithm>

// C includes
#include <cassert>

// Z3 includes
#include "z3++.h"

// Project includes
#include "conjecture.h"
#include "decision_tree.h"
#include "horn_constraint.h"
#include "horn_counterexample.h"
#include "z3_helper.h"
#include "../../hice-dt/include/datapoint.h"
#include "datapoint.h"
#include "api.h"
#include "dt_to_z3_exp.h"
#include "pretty_print_visitor.h" // DEBUG

#define EXTRA_ATTR
#define DT
namespace chc_teacher
{
	
	/**
	 * This class implements an interface to the lerning algorithm.
	 */

	class learner_interface
	{

		struct datapoint_Hasher
		{

			unsigned operator() (const chc_teacher::datapoint & dp) const
			{
				return dp.hash();
			}

		};

		struct datapoint_Comparer
		{

			bool operator() (const chc_teacher::datapoint & dp1, const chc_teacher::datapoint & dp2) const
			{
				return dp1.equal(dp2);
			}

		};

		/// ID of relations
		std::unordered_map<z3::func_decl, unsigned, ASTHasher, ASTComparer> relation2ID;

		std::unordered_map<unsigned, z3::func_decl> categorical_identifier_to_relation;

		/// ID of attributes
		std::unordered_map<z3::func_decl, unsigned, ASTHasher, ASTComparer> relation_to_base_value;

		std::unordered_map<unsigned, z3::expr> integer_identifier_to_attribute;

		mutable std::unordered_map<chc_teacher::datapoint, horn_verification::datapoint<bool>, datapoint_Hasher, datapoint_Comparer> teacher_datapoint_to_learner_datapoint;

		/// Variables used to construct conjecture expressions
		std::vector<std::vector<z3::expr>> variables;

		horn_verification::api api_object;

		unsigned categorical_identifier;

		unsigned integer_identifier;

	public:

		/**
		 * Creates a new learner interface (and potentially the learner within in).
		 *
		 * @param relations The uninterpreted predicates that need to be learned
		 */
		learner_interface(const decl_set & relations, bool do_horndini_prephase, bool use_bounds) {

		  std::cout << "In " << __FUNCTION__ << "\n";
			categorical_identifier = 0;

			integer_identifier = 0;
			
			// For Horndini Prephase

			api_object.reserve_datapoint_ptrs(2000);

			api_object.configure_learner(do_horndini_prephase, use_bounds);

			unsigned left;

			//
			// Check number of argument of predicates
			//
			std::cout << __FUNCTION__ << ":: relations in the CHCs : \n";
			for (const auto & decl : relations)
			{
				std::cout << decl << "\n";
				if (decl.arity() == 0)
				{
					throw std::runtime_error("Uninterpreted predicates with no arguments are not allowed");
				}
			}
			
			//
			// Do seomthing with the uninterpreted predicated here (i.e., set of an order and store the number of arguments)
			//
			
			for (const auto & decl : relations)
			{
				//
				// Assign unique ID to relation
				//
				relation2ID.emplace(decl, categorical_identifier);

				std::cout << __FUNCTION__ << " :: Relation : " << decl << " is mapped to CatID :  " << categorical_identifier << "\n";

				categorical_identifier_to_relation.emplace(categorical_identifier, decl);

				std::cout << __FUNCTION__ << "CatID : " << categorical_identifier << " is mapped to Relation : " << decl << "\n";

				// TODO: Perhaps we also want to store the arity of each relation so as to easily compute the position of data in a DT data point object
			
				relation_to_base_value.emplace(decl, integer_identifier);

				std::cout << __FUNCTION__ << "Relation : " << decl << " is mapped to baseval :  " << integer_identifier << "\n";

				z3::context c;

				//
				// Create variables / expression for each argument of the relation
				//
				std::vector<z3::expr> attributes;
				attributes.reserve(decl.arity());

				left = integer_identifier;

				//
				// Adding primitive attributes
				//
				for (unsigned i = 0; i < decl.arity(); ++i) {

					auto attributeSort = decl.domain(i);
					auto attributeName = decl.name().str() + "#" + std::to_string(i);

					attributes.push_back(decl.ctx().constant(attributeName.c_str(), attributeSort));
					integer_identifier_to_attribute.emplace(integer_identifier++, decl.ctx().constant(attributeName.c_str(), attributeSort));
					std::cout << "Attribute Identifier : " << integer_identifier << " attribute : " << attributeName.c_str() << attributeSort << "\n";

					api_object.add_integer_attribute(attributeName);

				}		

#ifdef EXTRA_ATTR
				
				//adding derived attributes
				if(decl.arity() > 2)
				  {
				    for (unsigned first_index = 0; first_index < attributes.size(); first_index++) {
				      for (unsigned second_index = first_index+1; second_index < attributes.size(); second_index++) {
					for (unsigned third_index = first_index+2; third_index < attributes.size(); third_index++) {
					  if (attributes.at(first_index).get_sort().is_int() && attributes.at(second_index).get_sort().is_int()&& attributes.at(third_index).get_sort().is_int()) {

					    std::vector<int> numbers;
					    numbers.push_back(first_index);
					    numbers.push_back(second_index);
					    numbers.push_back(third_index);

					    std::sort(numbers.begin(), numbers.end());

					    // Generate all permutations using next_permutation
					    do {
					      std::stringstream firstAttributeStream, secondAttributeStream, thirdAttributeStream;
					      firstAttributeStream << attributes.at(numbers[0]);
					      secondAttributeStream << attributes.at(numbers[1]);
					      thirdAttributeStream << attributes.at(numbers[2]);

					      //==================
					      integer_identifier_to_attribute.emplace(integer_identifier++, attributes.at(numbers[0]) + attributes.at(numbers[1])+attributes.at(numbers[2]));
					      api_object.add_integer_attribute(firstAttributeStream.str() + "+" + secondAttributeStream.str() + "+" + thirdAttributeStream.str());
					      std::cout << __FUNCTION__ << "Derived Attribute Identifier : " << integer_identifier << " Derived attribute : " << attributes.at(numbers[0]) + attributes.at(numbers[1]) + attributes.at(numbers[2]) << "\n";

					      //==================					      
					      integer_identifier_to_attribute.emplace(integer_identifier++, attributes.at(numbers[0]) - attributes.at(numbers[1])-attributes.at(numbers[2]));
					      api_object.add_integer_attribute(firstAttributeStream.str() + "-" + secondAttributeStream.str() + "-" + thirdAttributeStream.str());
					      std::cout << __FUNCTION__ << "Derived Attribute Identifier : " << integer_identifier << " Derived attribute : " << attributes.at(numbers[0]) - attributes.at(numbers[1]) - attributes.at(numbers[2]) << "\n";

					      //==================
					      integer_identifier_to_attribute.emplace(integer_identifier++, attributes.at(numbers[0]) + attributes.at(numbers[1])-attributes.at(numbers[2]));
					      api_object.add_integer_attribute(firstAttributeStream.str() + "+" + secondAttributeStream.str() + "-" + thirdAttributeStream.str());
					      std::cout << __FUNCTION__ << "Derived Attribute Identifier : " << integer_identifier << " Derived attribute : " << attributes.at(numbers[0]) + attributes.at(numbers[1]) - attributes.at(numbers[2]) << "\n";

					      //==================
					      integer_identifier_to_attribute.emplace(integer_identifier++, attributes.at(numbers[0]) - attributes.at(numbers[1])+attributes.at(numbers[2]));
					      api_object.add_integer_attribute(firstAttributeStream.str() + "-" + secondAttributeStream.str() + "+" + thirdAttributeStream.str());
					      std::cout << __FUNCTION__ << "Derived Attribute Identifier : " << integer_identifier << " Derived attribute : " << attributes.at(numbers[0]) - attributes.at(numbers[1]) + attributes.at(numbers[2]) << "\n";

					    } while (std::next_permutation(numbers.begin(), numbers.end()));
					  }
					}
				      }
				    }
				  }
#endif				
				
				// if( decl.name().str() == "inv2") {
				// 	std::stringstream firstAttributeStream, secondAttributeStream, thirdAttributeStream;

				// 	firstAttributeStream << attributes.at(1);
				// 	secondAttributeStream << attributes.at(2);
				// 	thirdAttributeStream << attributes.at(3);

				// 	integer_identifier_to_attribute.emplace(integer_identifier++, attributes.at(3) + attributes.at(2) - attributes.at(1));
				// 	std::cout << __FUNCTION__ << "Derived Attribute Identifier : " << integer_identifier << " Derived attribute : " << attributes.at(3) + attributes.at(2) - attributes.at(1) << "args::"<< (attributes.at(3) + attributes.at(2) - attributes.at(1)).arg(0) <<"\n";
				// 	api_object.add_integer_attribute(thirdAttributeStream.str() + "+" + secondAttributeStream.str() + "-" + firstAttributeStream.str());
				// }

				// if( decl.name().str() == "inv1") {
				// 	std::stringstream firstAttributeStream, secondAttributeStream, thirdAttributeStream;

				// 	firstAttributeStream << attributes.at(1);
				// 	secondAttributeStream << attributes.at(2);
				// 	thirdAttributeStream << attributes.at(3);

				// 	integer_identifier_to_attribute.emplace(integer_identifier++, attributes.at(3) + attributes.at(2) - attributes.at(1));
				// 	std::cout << __FUNCTION__ << "Derived Attribute Identifier : " << integer_identifier << " Derived attribute : " << attributes.at(3) + attributes.at(2) - attributes.at(1) << "\n";
				// 	api_object.add_integer_attribute(thirdAttributeStream.str() + "+" + secondAttributeStream.str() + "-" + firstAttributeStream.str());
				// }


				//
				// Adding derived attributes
				//

				for (unsigned first_index = 0; first_index < attributes.size(); first_index++) {

					for (unsigned second_index = first_index + 1; second_index < attributes.size(); second_index++) {

						if (attributes.at(first_index).get_sort().is_int() && attributes.at(second_index).get_sort().is_int()) {

							std::stringstream firstAttributeStream, secondAttributeStream;

							firstAttributeStream << attributes.at(first_index);
							secondAttributeStream << attributes.at(second_index);

							integer_identifier_to_attribute.emplace(integer_identifier++, attributes.at(first_index) + attributes.at(second_index));


							api_object.add_integer_attribute(firstAttributeStream.str() + "+" + secondAttributeStream.str());
							std::cout << __FUNCTION__ << "Derived Attribute Identifier : " << integer_identifier << " Derived attribute : " << attributes.at(first_index) + attributes.at(second_index) << "\n";

							integer_identifier_to_attribute.emplace(integer_identifier++, attributes.at(first_index) - attributes.at(second_index));

							api_object.add_integer_attribute(firstAttributeStream.str() + "-" + secondAttributeStream.str());
							std::cout << __FUNCTION__ << "Derived Attribute Identifier : " << integer_identifier << " Derived attribute : " << attributes.at(first_index) - attributes.at(second_index) << "\n";
							

						}
					}
				}
				variables.push_back(std::move(attributes));
				categorical_identifier++;
				api_object.add_intervals(left, (integer_identifier - 1));
			}
			api_object.add_categorical_attribute("$func", categorical_identifier);
		}

	horn_verification::datapoint<bool>* get_unique_learner_datapoint(const chc_teacher::datapoint &teacher_datapoint) const {
		std::cout << "In::" << __FUNCTION__ <<"\n";
			std::cout << "=============\n";
	  std::cout << __FUNCTION__ << "::Current Teacher Datapoint: " << teacher_datapoint << "\n";
		if (teacher_datapoint_to_learner_datapoint.find(teacher_datapoint) == teacher_datapoint_to_learner_datapoint.end()) { 

			horn_verification::datapoint<bool> current_learner_datapoint(api_object.index_of_datapoint_ptrs());

			horn_verification::attributes_metadata md = api_object.get_metadata();
			
			current_learner_datapoint._int_data = teacher_datapoint.get_int_data(relation_to_base_value, integer_identifier);
				
			current_learner_datapoint._categorical_data = teacher_datapoint.get_categorical_data(relation2ID);

			// for (auto const &i : current_learner_datapoint._categorical_data){
			//   std::cout << __FUNCTION__ << ":: Printing category data: " << i << "\n";
			// }
			// std::cout << "Current Learner Categorical data : " << current_learner_datapoint._categorical_data << "\n";
			std::cout << __FUNCTION__ << ":: Current Teacher Datapoint: " << teacher_datapoint << "\n";
			// std::cout << __FUNCTION__ << ":: Current Learner Datapoint: " << current_learner_datapoint << "\n";
				
			teacher_datapoint_to_learner_datapoint.emplace(teacher_datapoint, current_learner_datapoint);

			//assert (teacher_datapoint_to_learner_datapoint.find(teacher_datapoint)->second._categorical_data.size() == 1);

			if (teacher_datapoint_to_learner_datapoint.find(teacher_datapoint)->second._identifier == api_object.index_of_datapoint_ptrs()) {

			// This portion to re investigate why the teacher_datapoint is mapping to an existing learner_datapoint
			// Hopefully there will be an unused datapoint

			// Some one can check whether teacher_datapoint_to_learner_datapoint can be a pair or vectors rather than a Map

				api_object.add_datapoints(teacher_datapoint_to_learner_datapoint.find(teacher_datapoint)->second);
			}
		}

		return &teacher_datapoint_to_learner_datapoint.find(teacher_datapoint)->second;
	}


		/**
		 * Adds a new counterexample  to the sample.
		 *
		 * @param counterexample A pair of lists of data points representing a
		 *                       Horn counterexample. Positive and negative counterexamples
		 *                       are also given in Horn form with empty left-hand-side and
		 *                       empty right-hand-side, respectively.
		 *
		 * @returns Returns whether the current counterexample already exists in the sample.
		 */
		bool add_counterexample(const horn_counterexample & counterexample)
		{
		  std::cout << "In::"<< __FUNCTION__ << "\n";
		        //
			// This function should distinguish between real Horn counterexamples or positive
			// counterexamples (left-hand-side is empty) or negative counterexample
			// (right-hand-side is empty).
			//
			
			//
			// Example to distinguish types of counterexamples
			//
			
			//	Positive counterexample
			if (counterexample.lhs.size() == 0 && counterexample.rhs.size() == 1) {

			  // for (auto &rhs : counterexample.rhs){
			  //   std::cout << "Printing the current counterexample :" << rhs << "\n";			    
			  // }

			  std::cout << __FUNCTION__ << " Current counterexample : " << counterexample << "\n";
			  std::cout << __FUNCTION__ <<" Current teacher datapoint : " << *(counterexample.rhs.begin()) << "\n";
			  
			  horn_verification::datapoint<bool> *current_learner_datapoint = get_unique_learner_datapoint(*(counterexample.rhs.begin()));

			  std::cout << __FUNCTION__ <<" Current teacher datapoint(Positive) : " << *(counterexample.rhs.begin()) << "\n";
			  // std::cout << __FUNCTION__ <<" Current learner datapoint(Positive) : " << *current_learner_datapoint << "\n";
				if (current_learner_datapoint->_is_classified == true) {

					if (current_learner_datapoint->_classification == false) {

						throw std::runtime_error("Contradicting counterexample");
					}
				} else {

					current_learner_datapoint->set_classification(true);
				}
			}

			//	Negative counterexample
			else if (counterexample.lhs.size() == 1 && counterexample.rhs.size() == 0) {

				horn_verification::datapoint<bool> *current_learner_datapoint = get_unique_learner_datapoint(*(counterexample.lhs.begin()));
				std::cout << __FUNCTION__ <<" Current teacher datapoint(Negative) : " << *(counterexample.lhs.begin()) << "\n";
				// std::cout << __FUNCTION__ <<" Current learner datapoint(Negative) : " << *current_learner_datapoint << "\n";

				
				if (current_learner_datapoint->_is_classified == true) {

					if (current_learner_datapoint->_classification == true) {

						throw std::runtime_error("Contradicting counterexample");
					}
				} else {

					current_learner_datapoint->set_classification(false);
				}
			}

			// Horn counterexample
			else if (counterexample.lhs.size() > 0 && counterexample.rhs.size() <= 1) {

				std::vector<horn_verification::datapoint<bool> *> lhs_of_horn;

				horn_verification::datapoint<bool> *rhs_of_horn = NULL;

				/* Unsigned datapoints*/

				if (counterexample.rhs.size() == 1) {

					rhs_of_horn = get_unique_learner_datapoint(*(counterexample.rhs.begin()));

					/* return intervals */
				}

				for (auto const& current_datapoint : counterexample.lhs) {

					lhs_of_horn.push_back(get_unique_learner_datapoint(current_datapoint));
				}

				horn_verification::horn_constraint<bool> horn_constraint(lhs_of_horn, rhs_of_horn, false);
				std::cout << __FUNCTION__ <<" Current teacher datapoint(horn) : " << counterexample << "\n";
				// std::cout << __FUNCTION__ <<" Current learner datapoint(horn) : " << horn_constraint << "\n";
				
				api_object.add_horn_constraints(horn_constraint);
			}

			// Malformed counterexample
			else {

				throw std::runtime_error("Malformed counterexample");
			}
			
			return true;
		}
		
		/**
		 * Generates (i.e., learns) a new set of conjectures that is consistent with
		 * the current sample.
		 *
		 * @return a map that maps declarations of the uninterpreted predicates to their
		 *         implementation in form of a conjecture object.
		 */
		std::unordered_map<z3::func_decl, conjecture, ASTHasher, ASTComparer> get_conjectures()
		{
		        std::cout << "In :: " << __FUNCTION__ << "\n";
			auto decision_tree = api_object.learn_decision_tree();

			horn_verification::pretty_print_visitor printer;

#ifdef DT
			std::cout << __FUNCTION__ << ":: Printing the Decision Tree\n";
			decision_tree.accept(printer);
			std::cout << "\n";
#endif
			//std::cout << "Hi" << std::endl;

			// std::cout << "Call to map_dt_z3\n";
			//
			// std::cout << __FUNCTION__ << ":: Variables\n";
			// for (auto const &var : variables) {
			// 	for (auto const &v : var) {
			// 		std::cout << " Variable :: " << v << "\n";
			// 	}
			// }
			//
			// std::cout << __FUNCTION__ << ":: Categorical Vars\n";
			// for (auto const &cats : categorical_identifier_to_relation) {
			// 		std::cout << " Int :: " << cats.first << "decl : " << cats.second << "\n";
			// }
			//
			// int int_attr_no = 0;
			// std::cout << __FUNCTION__ << ":: Integer Vars\n";
			// for (auto const &ints : integer_identifier_to_attribute) {
			// 	std::cout << " CAT :: " << ints.first << "expr : " << ints.second << "\n";
			// 	std::cout << "Printed Attribute :: " << int_attr_no++ << "\n";
			// }

			// std::cout << "Done Printing\n";
			dt_to_z3_exp map_dt_z3(variables, categorical_identifier_to_relation, integer_identifier_to_attribute);

			std::cout << "Return from map_dt_z3\n";
			return map_dt_z3.get_unordered_map(decision_tree.root());
		}

	};

}; // End namespace chc_teacher

#endif
