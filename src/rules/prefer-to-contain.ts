import {
  AST_NODE_TYPES,
  TSESLint,
  TSESTree,
} from '@typescript-eslint/experimental-utils';
import {
  CallExpressionWithSingleArgument,
  KnownCallExpression,
  ModifierName,
  NotNegatableParsedModifier,
  ParsedEqualityMatcherCall,
  ParsedExpectMatcher,
  createRule,
  getAccessorValue,
  hasOneArgument,
  isExpectCall,
  isParsedEqualityMatcherCall,
  isSupportedAccessor,
  parseExpectCall,
} from './utils';

interface BooleanLiteral extends TSESTree.Literal {
  value: boolean;
}

const isBooleanLiteral = (node: TSESTree.Node): node is BooleanLiteral =>
  node.type === AST_NODE_TYPES.Literal && typeof node.value === 'boolean';

type ParsedBooleanEqualityMatcherCall = ParsedEqualityMatcherCall<
  BooleanLiteral
>;

/**
 * Checks if the given `ParsedExpectMatcher` is a call to one of the equality matchers,
 * with a boolean literal as the sole argument.
 *
 * @example javascript
 * toBe(true);
 * toEqual(false);
 *
 * @param {ParsedExpectMatcher} matcher
 *
 * @return {matcher is ParsedBooleanEqualityMatcher}
 */
const isBooleanEqualityMatcher = (
  matcher: ParsedExpectMatcher,
): matcher is ParsedBooleanEqualityMatcherCall =>
  isParsedEqualityMatcherCall(matcher) &&
  isBooleanLiteral(matcher.arguments[0]);

type FixableIncludesCallExpression = KnownCallExpression<'includes'> &
  CallExpressionWithSingleArgument;

/**
 * Checks if the given `node` is a `CallExpression` representing the calling
 * of an `includes`-like method that can be 'fixed' (using `toContain`).
 *
 * @param {CallExpression} node
 *
 * @return {node is FixableIncludesCallExpression}
 *
 * @todo support `['includes']()` syntax (remove last property.type check to begin)
 * @todo break out into `isMethodCall<Name extends string>(node: TSESTree.Node, method: Name)` util-fn
 */
const isFixableIncludesCallExpression = (
  node: TSESTree.Node,
): node is FixableIncludesCallExpression =>
  node.type === AST_NODE_TYPES.CallExpression &&
  node.callee.type === AST_NODE_TYPES.MemberExpression &&
  isSupportedAccessor(node.callee.property) &&
  getAccessorValue(node.callee.property) === 'includes' &&
  node.callee.property.type === AST_NODE_TYPES.Identifier &&
  hasOneArgument(node);

const buildToContainFuncExpectation = (negated: boolean) =>
  negated ? `${ModifierName.not}.toContain` : 'toContain';

/**
 * Finds the first `.` character token between the `object` & `property` of the given `member` expression.
 *
 * @param {TSESTree.MemberExpression} member
 * @param {SourceCode} sourceCode
 *
 * @return {Token | null}
 */
const findPropertyDotToken = (
  member: TSESTree.MemberExpression,
  sourceCode: TSESLint.SourceCode,
) =>
  sourceCode.getFirstTokenBetween(
    member.object,
    member.property,
    token => token.value === '.',
  );

const getNegationFixes = (
  node: FixableIncludesCallExpression,
  modifier: NotNegatableParsedModifier,
  matcher: ParsedBooleanEqualityMatcherCall,
  sourceCode: TSESLint.SourceCode,
  fixer: TSESLint.RuleFixer,
  fileName: string,
) => {
  //.includes function argument
  const [containArg] = node.arguments;
  const negationPropertyDot = findPropertyDotToken(modifier.node, sourceCode);

  const toContainFunc = buildToContainFuncExpectation(
    matcher.arguments[0].value,
  );
  // ? 'not.toContain'
  // : 'toContain';

  /* istanbul ignore next */
  if (negationPropertyDot === null) {
    throw new Error(
      `Unexpected null when attempting to fix ${fileName} - please file a github issue at https://github.com/jest-community/eslint-plugin-jest`,
    );
  }

  return [
    fixer.remove(negationPropertyDot),
    fixer.remove(modifier.node.property),
    fixer.replaceText(matcher.node.property, toContainFunc),
    fixer.replaceText(matcher.arguments[0], sourceCode.getText(containArg)),
  ];
};

const getCommonFixes = (
  node: FixableIncludesCallExpression,
  sourceCode: TSESLint.SourceCode,
  fixer: TSESLint.RuleFixer,
  fileName: string,
) => {
  const [containArg] = node.arguments;
  const includesCallee = node.callee;

  const propertyDot = findPropertyDotToken(includesCallee, sourceCode);

  const closingParenthesis = sourceCode.getTokenAfter(containArg);
  const openParenthesis = sourceCode.getTokenBefore(containArg);

  /* istanbul ignore next */
  if (
    propertyDot === null ||
    closingParenthesis === null ||
    openParenthesis === null
  ) {
    throw new Error(
      `Unexpected null when attempting to fix ${fileName} - please file a github issue at https://github.com/jest-community/eslint-plugin-jest`,
    );
  }

  return [
    fixer.remove(containArg),
    fixer.remove(includesCallee.property),
    fixer.remove(propertyDot),
    fixer.remove(closingParenthesis),
    fixer.remove(openParenthesis),
  ];
};
// expect(array.includes(<value>)[not.]{toBe,toEqual}(<boolean>)
export default createRule({
  name: __filename,
  meta: {
    docs: {
      category: 'Best Practices',
      description: 'Suggest using `toContain()`',
      recommended: false,
    },
    messages: {
      useToContain: 'Use toContain() instead',
    },
    fixable: 'code',
    type: 'suggestion',
    schema: [],
  },
  defaultOptions: [],
  create(context) {
    return {
      CallExpression(node) {
        if (!isExpectCall(node)) {
          return;
        }

        const {
          expect: {
            arguments: [includesCall],
          },
          matcher,
          modifier,
        } = parseExpectCall(node);

        if (
          !matcher ||
          (modifier && modifier.name !== ModifierName.not) ||
          !isBooleanEqualityMatcher(matcher) ||
          !isFixableIncludesCallExpression(includesCall)
        ) {
          return;
        }

        context.report({
          fix(fixer) {
            const sourceCode = context.getSourceCode();
            const fileName = context.getFilename();

            const fixArr = getCommonFixes(
              includesCall,
              sourceCode,
              fixer,
              fileName,
            );

            if (modifier && modifier.name === ModifierName.not) {
              return getNegationFixes(
                includesCall,
                modifier,
                matcher,
                sourceCode,
                fixer,
                fileName,
              ).concat(fixArr);
            }

            const toContainFunc = buildToContainFuncExpectation(
              !matcher.arguments[0].value,
            );

            //.includes function argument
            const [containArg] = includesCall.arguments;

            fixArr.push(
              fixer.replaceText(matcher.node.property, toContainFunc),
            );
            fixArr.push(
              fixer.replaceText(
                matcher.arguments[0],
                sourceCode.getText(containArg),
              ),
            );
            return fixArr;
          },
          messageId: 'useToContain',
          node: (modifier || matcher).node.property,
        });
      },
    };
  },
});