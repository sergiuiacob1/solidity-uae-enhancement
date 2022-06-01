/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0
/**
 * Optimiser component that removes assignments to variables that are not used
 * until they go out of scope or are re-assigned.
 */

#include <iostream>
#include <libyul/AsmPrinter.h>
#include <libyul/optimiser/UnusedAssignEliminator.h>

#include <libyul/AST.h>
#include <libyul/optimiser/OptimizerUtilities.h>
#include <libyul/optimiser/Semantics.h>

#include <libsolutil/CommonData.h>

#include <range/v3/action/remove_if.hpp>

using namespace std;
using namespace solidity;
using namespace solidity::yul;

void UnusedAssignEliminator::run(OptimiserStepContext& _context, Block& _ast)
{
	UnusedAssignEliminator rae{_context.dialect};
	rae(_ast);

	StatementRemover remover{rae.m_pendingRemovals};
	remover(_ast);
}

void UnusedAssignEliminator::operator()(Identifier const& _identifier)
{
	changeUndecidedTo(_identifier.name, State::Used);
}

void UnusedAssignEliminator::operator()(VariableDeclaration const& _variableDeclaration)
{
	UnusedStoreBase::operator()(_variableDeclaration);

	for (auto const& var: _variableDeclaration.variables)
		m_declaredVariables.emplace(var.name);
}

void UnusedAssignEliminator::operator()(Assignment const& _assignment)
{
	visit(*_assignment.value);
	for (auto const& var: _assignment.variableNames)
		changeUndecidedTo(var.name, State::Unused);
}

void UnusedAssignEliminator::operator()(FunctionDefinition const& _functionDefinition)
{
	ScopedSaveAndRestore outerDeclaredVariables(m_declaredVariables, {});
	ScopedSaveAndRestore outerReturnVariables(m_returnVariables, {});

	for (auto const& retParam: _functionDefinition.returnVariables)
		m_returnVariables.insert(retParam.name);

	UnusedStoreBase::operator()(_functionDefinition);
}

void UnusedAssignEliminator::operator()(Leave const&)
{
	cout << "am dat visit la leave"
		 << "\n";
	for (YulString name: m_returnVariables)
		changeUndecidedTo(name, State::Used);

	// TODO all assignments that are undecided should be marked as unused
	// for
}

// TrackedStore == std::map<YulString, std::map<Statement const*, State>>;
void UnusedAssignEliminator::getNewAssignmentsInBlock(
	TrackedStores const& outerScopeStores, TrackedStores & blockScopeStores)
{
	cout << "verific new assignments\n";
	for (auto it = blockScopeStores.begin(); it != blockScopeStores.end(); it++)
	{
		auto varName = it->first;
		// cout << "verific " << varName.str() << "\n";
		if (!outerScopeStores.count(varName))
		{
			// cout << "new var in town: " << varName.str() << "\n";
			// this is a newly declared variable – will be handled by the UnusedPruner, if necessary
			// using namespace solidity::util;
			// YulString const* oldValue = util::valueOrNullptr(_older, key);
		}
		else
		// TODO ce se intampla daca am acelasi assignment si in outer scope, si in block scope?
		// acelasi gen aceeasi_var = aceeasi_val
		{
			// search for new assignments
			std::map<Statement const*, State> blockScopeStatements = blockScopeStores.at(varName);
			std::map<Statement const*, State> outerScopeStatements = outerScopeStores.at(varName);
			for (auto stmtIterator = blockScopeStatements.begin(); stmtIterator != blockScopeStatements.end();
				 stmtIterator++)
			{
				Statement const* stmt = stmtIterator->first;
				if (!outerScopeStatements.count(stmt))
				{
					// cout << "mark " << varName.str() << " cu state-ul "
						//  << stmtIterator->second.getValue() << "\n";
					if (std::strcmp(stmtIterator->second.getValue(), "Undecided") == 0){
						std::visit([](const auto& var) { cout << "marked stmt " << AsmPrinter()(var) << " as unused\n"; }, *stmt);
						// stmtIterator->second = State::Unused;
						blockScopeStatements[stmt] = State::Unused;
						blockScopeStores[varName] = blockScopeStatements;
					}
				}
			}

			// auto varStatements = blockScopeStores.find(varName).second;
			// for (auto blockAssignStmt = varStatements.begin(); blockAssignStmt != varStatements.end();
			// blockAssignStmt++)
		}
	}

	cout << "printing stores right after marking that shit as undecided\n";
	UnusedAssignEliminator::printTrackedStores(blockScopeStores);
	// return null;
}

void UnusedAssignEliminator::operator()(Block const& _block)
{
	ScopedSaveAndRestore outerDeclaredVariables(m_declaredVariables, {});


	// _block.statements.empty() ||
	// 	// TODO 2nd parameter was &m_controlFlowSideEffects

	cout << "visiting block " << AsmPrinter()(_block) << "\n";

	TrackedStores beforeBlockVisitStores{m_stores};

	if (!_block.statements.empty())
	{
		TerminationFinder::ControlFlow controlFlowKind = TerminationFinder{this->m_dialect}.controlFlowKind(
			_block.statements.back()); // == TerminationFinder::ControlFlow::FlowOut;
		if (controlFlowKind == TerminationFinder::ControlFlow::Terminate)
		{
			cout << "am gasit termination Terminate\n";
		}
		else if (controlFlowKind == TerminationFinder::ControlFlow::FlowOut)
		{
			cout << "am gasit termination FlowOut\n";
		}
		else if (controlFlowKind == TerminationFinder::ControlFlow::Leave)
		{
			cout << "am gasit termination Leave\n";
		}
		else
		{
			cout << "Am gasit un alt fel de termination\n";
		}
	}
	else
	{
		cout << "block has no statements\n";
	}

	UnusedStoreBase::operator()(_block);

	// cout << "Printing tracked stores...\n";
	// for (auto it = this->m_stores.begin(); it != this->m_stores.end(); it++) {
	// 	cout << (*it).first.str() << " ";
	// }
	// cout << "\n";

	// TODO sa scriu de ce nu mergea sa pun pe unused aici – daca mai e cazul
	this->getNewAssignmentsInBlock(beforeBlockVisitStores, this->m_stores);

	cout << "Printing tracked stores before UnusedStoreBase visited...\n";
	UnusedAssignEliminator::printTrackedStores(beforeBlockVisitStores);
	cout << "Printing tracked stores after UnusedStoreBase visited...\n";
	UnusedAssignEliminator::printTrackedStores(this->m_stores);



	// cout << "Printing declared variables after UnusedStoreBase visited...\n";
	// for (auto it = this->m_declaredVariables.begin(); it != this->m_declaredVariables.end(); it++) {
	// 	cout << (*it).str() << " ";
	// }
	// cout << "\n";

	cout << "\n\n\n";

	for (auto const& var: m_declaredVariables)
		finalize(var, State::Unused);
}

void UnusedAssignEliminator::printTrackedStores(TrackedStores const& stores) {
	for (auto it = stores.begin(); it != stores.end(); it++)
	{
		auto varName = it->first.str();
		cout << "\t" << varName << "\n";
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
		{
			Statement const* stmt = it2->first;
			std::visit([](const auto& var) { cout << "\t\t" << AsmPrinter()(var); }, *stmt);
			cout << " --- " << it2->second.getValue() << "\n";
		}
	}
	cout << "\n";
}


void UnusedAssignEliminator::visit(Statement const& _statement)
{
	UnusedStoreBase::visit(_statement);

	// LEFT: , , , Switch, ForLoop, Break, Continue, Leave, Block
	// std::visit(
	// 	[](const auto& var)
	// 	{
	// 		if constexpr (std::is_same_v<std::decay_t<decltype(var)>, ExpressionStatement>)
	// 		{
	// 			cout << "am un ExpressionStatement\n";
	// 		}
	// 		else if constexpr (std::is_same_v<std::decay_t<decltype(var)>, Assignment>)
	// 		{
	// 			cout << "am un Assignment\n";
	// 			cout << AsmPrinter()(var) << "\n";
	// 		}
	// 		else if constexpr (std::is_same_v<std::decay_t<decltype(var)>, VariableDeclaration>)
	// 		{
	// 			cout << "am un VariableDeclaration\n";
	// 			cout << AsmPrinter()(var) << "\n";
	// 		}
	// 		else if constexpr (std::is_same_v<std::decay_t<decltype(var)>, FunctionDefinition>)
	// 		{
	// 			cout << "am un FunctionDefinition\n";
	// 		}
	// 		else if constexpr (std::is_same_v<std::decay_t<decltype(var)>, If>)
	// 		{
	// 			cout << "am un If\n";
	// 		}
	// 	},
	// 	_statement);

	if (auto const* assignment = get_if<Assignment>(&_statement))
		if (assignment->variableNames.size() == 1)
		{
			// Default-construct it in "Undecided" state if it does not yet exist.
			m_stores[assignment->variableNames.front().name][&_statement];
			cout << "am adaugat new assignment in m_stores " << assignment->variableNames.front().name.str() << "\n";
		}
}

// TODO anything to do here?
void UnusedAssignEliminator::shortcutNestedLoop(TrackedStores const& _zeroRuns)
{
	// Shortcut to avoid horrible runtime:
	// Change all assignments that were newly introduced in the for loop to "used".
	// We do not have to do that with the "break" or "continue" paths, because
	// they will be joined later anyway.
	// TODO parallel traversal might be more efficient here.
	for (auto& [variable, stores]: m_stores)
		for (auto& assignment: stores)
		{
			auto zeroIt = _zeroRuns.find(variable);
			if (zeroIt != _zeroRuns.end() && zeroIt->second.count(assignment.first))
				continue;
			assignment.second = State::Value::Used;
		}
}

void UnusedAssignEliminator::finalizeFunctionDefinition(FunctionDefinition const& _functionDefinition)
{
	for (auto const& param: _functionDefinition.parameters)
		finalize(param.name, State::Unused);
	for (auto const& retParam: _functionDefinition.returnVariables)
		finalize(retParam.name, State::Used);
}

void UnusedAssignEliminator::changeUndecidedTo(YulString _variable, UnusedAssignEliminator::State _newState)
{
	for (auto& assignment: m_stores[_variable])
		if (assignment.second == State::Undecided)
			assignment.second = _newState;
}

void UnusedAssignEliminator::finalize(YulString _variable, UnusedAssignEliminator::State _finalState)
{
	std::map<Statement const*, State> stores = std::move(m_stores[_variable]);
	m_stores.erase(_variable);

	for (auto& breakAssignments: m_forLoopInfo.pendingBreakStmts)
	{
		util::joinMap(stores, std::move(breakAssignments[_variable]), State::join);
		breakAssignments.erase(_variable);
	}
	for (auto& continueAssignments: m_forLoopInfo.pendingContinueStmts)
	{
		util::joinMap(stores, std::move(continueAssignments[_variable]), State::join);
		continueAssignments.erase(_variable);
	}

	for (auto&& [statement, state]: stores)
		if ((state == State::Unused || (state == State::Undecided && _finalState == State::Unused))
			&& SideEffectsCollector{m_dialect, *std::get<Assignment>(*statement).value}.movable())
			m_pendingRemovals.insert(statement);
}
