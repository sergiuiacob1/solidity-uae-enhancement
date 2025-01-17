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
#include <libsolutil/CommonData.h>
#include <libsolutil/Visitor.h>
#include <libyul/AST.h>
#include <libyul/AsmPrinter.h>
#include <libyul/Utilities.h>
#include <libyul/optimiser/StructuralSimplifier.h>

using namespace std;
using namespace solidity;
using namespace solidity::yul;

using OptionalStatements = std::optional<vector<Statement>>;

namespace
{

OptionalStatements replaceConstArgSwitch(Switch& _switchStmt, u256 const& _constExprVal)
{
	Block* matchingCaseBlock = nullptr;
	Case* defaultCase = nullptr;

	for (auto& _case: _switchStmt.cases)
	{
		if (_case.value && valueOfLiteral(*_case.value) == _constExprVal)
		{
			matchingCaseBlock = &_case.body;
			break;
		}
		else if (!_case.value)
			defaultCase = &_case;
	}

	if (!matchingCaseBlock && defaultCase)
		matchingCaseBlock = &defaultCase->body;

	if (matchingCaseBlock)
		return util::make_vector<Statement>(std::move(*matchingCaseBlock));
	else
		return optional<vector<Statement>>{vector<Statement>{}};
}

optional<u256> hasLiteralValue(Expression const& _expression)
{
	if (holds_alternative<Literal>(_expression))
		return valueOfLiteral(std::get<Literal>(_expression));
	else
		return std::optional<u256>();
}

bool expressionAlwaysTrue(Expression const& _expression)
{
	if (std::optional<u256> value = hasLiteralValue(_expression))
		return *value != 0;
	else
		return false;
}

bool expressionAlwaysFalse(Expression const& _expression)
{
	if (std::optional<u256> value = hasLiteralValue(_expression))
		return *value == 0;
	else
		return false;
}

bool blockHasIfTerminationFlow(Block& _block)
{
	if (_block.statements.empty())
	{
		return false;
	}

	Statement& lastStmt = _block.statements.back();
	return std::visit(
		util::GenericVisitor{
			[&](If& _ifStmt) -> bool
			{
				if (_ifStmt.body.statements.size() != 1)
				{
					return false;
				}
				Statement const& _lastIfStmt = _ifStmt.body.statements.back();
				return std::visit(
					util::GenericVisitor{
						[&](Leave const&) -> bool { return true; },
						[&](auto const&) -> bool { return false; },
					},
					_lastIfStmt);
			},

			[&](auto const&) -> bool { return false; },
		},
		lastStmt);
}

OptionalStatements simplifyBlockTrailingIfTermination(FunctionDefinition& _funcDef)
{
	_funcDef.body.statements.pop_back();
	return {util::make_vector<Statement>(std::move(_funcDef))};
}

}

void StructuralSimplifier::run(OptimiserStepContext&, Block& _ast) { StructuralSimplifier{}(_ast); }

void StructuralSimplifier::operator()(Block& _block) { simplify(_block.statements); }

void StructuralSimplifier::simplify(std::vector<yul::Statement>& _statements)
{
	util::GenericVisitor visitor{
		util::VisitorFallback<OptionalStatements>{},
		[&](If& _ifStmt) -> OptionalStatements
		{
			if (expressionAlwaysTrue(*_ifStmt.condition))
				return {std::move(_ifStmt.body.statements)};
			else if (expressionAlwaysFalse(*_ifStmt.condition))
				return {vector<Statement>{}};
			return {};
		},
		[&](Switch& _switchStmt) -> OptionalStatements
		{
			if (std::optional<u256> const constExprVal = hasLiteralValue(*_switchStmt.expression))
				return replaceConstArgSwitch(_switchStmt, constExprVal.value());
			return {};
		},
		[&](ForLoop& _forLoop) -> OptionalStatements
		{
			if (expressionAlwaysFalse(*_forLoop.condition))
				return {std::move(_forLoop.pre.statements)};
			return {};
		},
		[&](FunctionDefinition& _funcDef) -> OptionalStatements
		{
			if (blockHasIfTerminationFlow(_funcDef.body))
			{
				return simplifyBlockTrailingIfTermination(_funcDef);
			}
			return {};

			if (!_funcDef.body.statements.empty())
			{
				Statement& lastStmt = _funcDef.body.statements.back();
				return std::visit(
					util::GenericVisitor{
						[&](If& _ifStmt) -> OptionalStatements
						{
							if (_ifStmt.body.statements.size() == 1)
							{
								Statement const& _lastIfStmt = _ifStmt.body.statements.back();
								bool hasLeave = std::visit(
									util::GenericVisitor{
										[&](Leave const&) -> bool { return true; },
										[&](auto const&) -> bool { return false; },
									},
									_lastIfStmt);
								if (hasLeave)
								{
									_funcDef.body.statements.pop_back();
									return {util::make_vector<Statement>(std::move(_funcDef))};
								}
							}
							return {};
						},

						[&](auto const&) -> OptionalStatements { return {}; },

					},
					lastStmt);
			}
			return {};
		}};

	util::iterateReplacing(
		_statements,
		[&](Statement& _stmt) -> OptionalStatements
		{
			OptionalStatements result = std::visit(visitor, _stmt);
			if (result)
				simplify(*result);
			else
				visit(_stmt);
			return result;
		});
}
