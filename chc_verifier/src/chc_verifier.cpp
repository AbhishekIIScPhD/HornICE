/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// C++ includes
#include <functional>
#include <iostream>
#include <list>
#include <chrono>
#include <ctime>
#include <getopt.h>
#include <unistd.h>

// Z3 includes
#include "z3++.h"

// Project includes
#include "seahorn_smtlib2_parser.h"
#include "chc_verifier.h"
#include "conjecture.h"
#include "learner_interface.h"

// #define DEBUG
// #define OTHER
#define CONJ
// #define CONJ_1

// #define COND if(learner_invocations == 57)

#define COND if(true)

#define INFUN std::cout<<"In "<<__FUNCTION__<<"\n"

using namespace chc_teacher;


void learn1(z3::context & ctx, const problem & p, bool do_horndini_prephase, bool use_bounds)
{
	learner_interface learner(p.relations, do_horndini_prephase, use_bounds);
	std::unordered_map<z3::func_decl, conjecture, ASTHasher, ASTComparer> previous_conjectures;
	bool finished = false;
	unsigned checked_chcs = 0;
	unsigned learner_invocations = 0;
	
	while (!finished)
	{		
		finished = true;
		
		// Get conjectures
		auto conjectures = learner.get_conjectures();
		++learner_invocations;
		
		
		//
		// Check each CHC and return counterexample if detected
		//
		for (const auto & chc : p.chcs)
		{
			
			// Check CHC
			auto counterexample = chc_verifier::check_chc(ctx, chc, conjectures);
			++checked_chcs;
			
			// If no counterexample was found, report success
			if (counterexample != nullptr)
			{
			
				learner.add_counterexample(*counterexample);
				finished = false;
				break;
			}

		}
		
		previous_conjectures = std::move(conjectures); // No use of conjectures beyond this point!		
		
	}

	
	assert (chc_verifier::naive_check(ctx, p, previous_conjectures) == nullptr);
	
	//
	// Output solution
	//
	// std::cout << "Success (checked " << checked_chcs << " CHCs, invoked learner " << learner_invocations << " times)" << std::endl;
	//for (const auto & c : previous_conjectures)
	{
		// std::cout << c.first << " => " << c.second << std::endl;				
	}
	
}


void learn2(z3::context & ctx, const problem & p, bool do_horndini_prephase, bool use_bounds)
{
  INFUN;
	// Prepare auxiliary variables and data structures
	learner_interface learner(p.relations, do_horndini_prephase, use_bounds);
	std::list<std::reference_wrapper<const constrainted_horn_clause>> satisfied_chcs;
	std::list<std::reference_wrapper<const constrainted_horn_clause>> unsatisfied_chcs;
	std::unordered_map<z3::func_decl, conjecture, ASTHasher, ASTComparer> previous_conjectures;
	unsigned checked_chcs = 0;
	unsigned learner_invocations = 0;
	std::list<std::unique_ptr<horn_counterexample>> all_counterexamples;	
	
	// All CHCs are unchecked
	for (const auto & chc : p.chcs)
	{
		unsatisfied_chcs.push_back(chc);
	}

	//
	// Run learning loop
	//
	while (!unsatisfied_chcs.empty())
	{
		std::cout << "===========================================\n";
		std::cout << "Learning Iteration: " << learner_invocations << "\n";
		std::cout << "===========================================\n";
		
		// Get conjectures
		auto conjectures = learner.get_conjectures();


		++learner_invocations;

#ifdef CONJ
		COND{
		  std::cout << "\n=========================\n";
		  std::cout << "Printing the conjectures" << "\n";

		  for (const auto& conjecture : conjectures) {
		    // std::cout << "Conjecture: " << "F : " << conjecture.first <<  "S : " << conjecture.second << "\n";
		    std::cout << "Conjecture: " << conjecture.first << conjecture.second << "\n";
		  }
		  std::cout << "=========================\n";
		}
#endif

#ifdef CONJ_1
		COND{
		std::cout << "\n=========================\n";
		std::cout << "Printing the previous conjectures" << "\n";

		for(auto const &prev_conj : previous_conjectures) {
			std::cout << "Prev Conjecture: " << prev_conj.first << prev_conj.second << "\n";
		}
		std::cout << "=========================\n";
		}
#endif

#ifdef DEBUG
		COND{
		std::cout << "\n\n=========================";
		std::cout << "\nPrinting Satisfied CHCs" << "\n";

		for(auto const &sat_chc : satisfied_chcs) {
			std::cout << "Satisfied CHC: " << sat_chc << "\n";
		}
		std::cout << "\n=========================\n";
		}
#endif

#ifdef DEBUG
		COND{
		std::cout << "=========================\n";
		std::cout << "Printing Unsatisfied CHCs" << "\n";

		for(auto const &unsat_chc : unsatisfied_chcs) {
			std::cout << "Unsatisfied CHC: " << unsat_chc << "\n";
		}
		std::cout << "=========================\n";
		}
#endif
		
		// Check which conjectures have changed
		std::unordered_map<z3::func_decl, bool, ASTHasher, ASTComparer> changed(conjectures.size());
		bool all_as_before = true;
		for (const auto & pair : conjectures)
		{
			
			// Get old conjecture for declaration (if exists)
			auto previous_conjecture_it = previous_conjectures.find(pair.first);
			
			// Store whether conjecture has changed
			auto has_changed = (previous_conjecture_it == previous_conjectures.end() || !(pair.second == previous_conjecture_it->second));
			changed[pair.first] = has_changed;
			if (has_changed)
			{
				all_as_before = false;
			}

		}

		//assert (!all_as_before);

		// DEBUG
		// std::cout << "---------- Changes of conjectures ----------" << std::endl;
		//for (const auto & status : changed)
		{
			// std::cout << status.first << ": " << status.second << std::endl;
		}
		// std::cout << "Unsatisfied CHCs: " << unsatisfied_chcs.size() << "; satisfied CHCs: " << satisfied_chcs.size() << std::endl;
		
		
		
		// Data structure to maintain counterexamples
		std::list<std::unique_ptr<horn_counterexample>> counterexamples;
		std::list<std::reference_wrapper<const constrainted_horn_clause>> now_satisfied_chcs;

		
		// Check previously unsatisfied chcs
		// std::cout << "++++++++++ UNSATISFIED CHCS ++++++++++" << std::endl;
		auto unsat_it = unsatisfied_chcs.begin();
		while (unsat_it != unsatisfied_chcs.end())
		{
			
			// Check whether a conjecture has changed
			bool has_changed = false;
			for (const auto & decl : unsat_it->get().uninterpreted_predicates)
			{
				if (changed.at(decl))
				{
					has_changed = true;
					break;
				}
			}
			
			
			// Check if some conjecture changed
			if (has_changed)
			{

				auto counterexample = chc_verifier::check_chc(ctx, *unsat_it, conjectures);
				++checked_chcs;
				
				// CHC is not satisfied, counterexample is returned
				if (counterexample != nullptr)
				{
#ifdef OTHER
				  COND{
					std::cout << "Unsatisfied (Previosuly Unsatisfied CHC): " << *unsat_it << "with counterexample :" << *counterexample <<"\n";
				  }
#endif
				  all_counterexamples.push_back(std::make_unique<horn_counterexample>(*counterexample));
				  counterexamples.push_back(std::move(counterexample)); // NO use of variable counterexample beyond this point
					
#ifdef OTHER_1
				  COND{
				    std::cout << "Unsat CHC Printing All Counterexamples" << "#" << counterexamples.size() << "\n";
				    for ( auto &cexam : counterexamples) {
				      std::cout << "Horn Counterexmple :" << *cexam << "\n";
				    }
				  }
#endif

					++unsat_it;
				}
				// CHC is now satisfied
				else
				{
					now_satisfied_chcs.push_back(*unsat_it);
#ifdef OTHER_1
					COND{
					std::cout << "Satisfied (Previously Unsatisfied CHC): " << *unsat_it << "\n";
					}
#endif
					unsat_it = unsatisfied_chcs.erase(unsat_it);
				}

			}
			else
			{
				++unsat_it;
				std::cout << "Unsat Formula";
			}
		}

		// Check previously satisfied CHC if it contains a conjecture that has changed in the last round
		// std::cout << "++++++++++ SATISFIED CHCS ++++++++++" << std::endl;
		auto sat_it = satisfied_chcs.begin();
		while (sat_it != satisfied_chcs.end())
		{
			
			// Check whether a conjecture has changed
			bool has_changed = false;
			for (const auto & decl : sat_it->get().uninterpreted_predicates)
			{
				if (changed.at(decl))
				{
					has_changed = true;
					break;
				}
			}
			
			// Check if some conjecture changed
			if (has_changed)
			{
				
				auto counterexample = chc_verifier::check_chc(ctx, *sat_it, conjectures);
				++checked_chcs;
				
				// CHC is not satisfied, counterexample is returned
				if (counterexample != nullptr)
				{
#ifdef OTHER
				  COND{
					std::cout << "Unsatisfied (Previously Satisfied CHC): " << *sat_it << "with counterexample :" << *counterexample << "\n";
				  }
#endif
				  all_counterexamples.push_back(std::make_unique<horn_counterexample>(*counterexample));
					counterexamples.push_back(std::move(counterexample)); // NO use of variable counterexample beyond this point
#ifdef OTHER_1
					COND{
					std::cout << "SatCHC Printing All Counterexample"  << "#" << counterexamples.size() << "\n";
					for ( auto &cexam : counterexamples) {
						std::cout << "Horn Counterexmple :" << *cexam << "\n";
					}
					}
#endif
					unsatisfied_chcs.push_back(*sat_it);
					sat_it = satisfied_chcs.erase(sat_it);
				}
				// CHC is now satisfied
				else
				{
#ifdef OTHER_1
				  COND{
					std::cout << "Satisfied (Previously Satisfied CHC): " << sat_it->get().expr << "\n";
				  }
#endif
					++sat_it;
				}
				
			}
			else
			{
				++sat_it;
			}
			
		}		
		
		
		// Add now satisfied CHCs
		satisfied_chcs.insert(satisfied_chcs.end(), std::make_move_iterator(now_satisfied_chcs.begin()), std::make_move_iterator(now_satisfied_chcs.end()));


#ifdef OTHER_1
		if(unsatisfied_chcs.empty()){
		  std::cout << "Printing all the counter examples : " << all_counterexamples.size() << "\n";
		  for (const auto &counter: all_counterexamples) {
		    std::cout << "Counterexample: " << *counter << "\n";
		  }		  
		}
#endif

		
		// Add counterexamples 		
		for (const auto & ce : counterexamples)
		{
			learner.add_counterexample(*ce);
		}
		
		previous_conjectures = std::move(conjectures); // No use of conjectures beyond this point!
	}


	
	assert (chc_verifier::naive_check(ctx, p, previous_conjectures) == nullptr);

	//
	// Output solution
	//
	std::cout << "Success (checked " << checked_chcs << " CHCs, invoked learner " << learner_invocations << " times)" << std::endl;
	for (const auto & c : previous_conjectures)
	{
	  std::cout << c.first << " => " << c.second << std::endl;
	  std::cout << "Simplified Formual\n";
#ifdef OTHER_1
	  std::cout << c.first << " => " << c.second.expr.simplify() << std::endl;
#endif
	}


    std::cout << "Final Relations read" << "\n";
	for (auto relation : p.relations) {
		std::cout << "Relation : " << relation.arity() << relation << relation.name() << "\n";
	}

	std::cout << "Final CHCs read" << "\n";
	for (auto ch : p.chcs) {
		for(auto pred : ch.predicates_in_lhs) {
			std::cout << "CHC : " << pred << "\n";
		}
	}
}



/**
 * Prints a help message to an output stream.
 *
 * @param out The output stream to write to
 * @param name The name of the program
 */
void print_help(std::ostream & out, const char * name)
{
	out << "Usage: " << name << " [options] file" << std::endl;
	out << "Options are:" << std::endl;
	out << "  -b\t\tBound the learner" << std::endl;
	out << "  -h\t\tRun Horndini pre-phase" << std::endl;
}


int main(int argc, char * argv[])
{


	/// Store the starting time of execution.
	 std::clock_t c_start = std::clock();


	//
	// Process command line arguments
	//
	bool do_horndini_prephase = false;
	bool use_bounds = false;

	int c;
	while ((c = getopt (argc, argv, "bh")) != -1)
	{

		switch (c)
		{
			case 'b':
				use_bounds = true;
				break;
				
			case 'h':
				do_horndini_prephase = true;
				break;

			default:
				print_help(std::cout, argv[0]);
				return EXIT_FAILURE;
		}

	}

	if (optind != argc-1)
	{
		std::cout << "Invalid input file specified" << std::endl;
		print_help(std::cout, argv[0]);
		return EXIT_FAILURE;
	}


	// File stem
	auto filename = std::string(argv[optind]);


	//
	// Create Z3 context and parse
	//
	z3::context ctx;
	auto p = seahorn_smtlib2_parser::parse(ctx, filename);
	std::cout << __FUNCTION__ << "::parsed \n"<< p << std::endl;

	std::cout << "Printing parse CHCs and relations\n";
	for(auto chc : p.chcs) {
		std::cout << "chc :: " << chc << "\n";
	}

	for(auto rel : p.relations) {
		std::cout << "rel :: " << rel << "\n";
	}
	//
	// Learn
	//
	//learn1(ctx, p); // Simple (original)
	learn2(ctx, p, do_horndini_prephase, use_bounds); // Improved?
	
	/// Store the finishing time of execution.
	std::clock_t c_end = std::clock();

	std::cout << "Total time: " << ((c_end-c_start)*100 / CLOCKS_PER_SEC)/100.00 << std::endl;

}
