import {
  AST_NODE_TYPES,
  ESLintUtils,
  TSESLint,
  TSESTree,
} from '@typescript-eslint/experimental-utils';
import { basename } from 'path';
import { version } from '../../package.json';

const REPO_URL = 'https://github.com/jest-community/eslint-plugin-jest';

export const createRule = ESLintUtils.RuleCreator(name => {
  const ruleName = basename(name, '.ts');
  return `${REPO_URL}/blob/v${version}/docs/rules/${ruleName}.md`;
});

/**
 * A `Literal` with a `value` of type `string`.
 */
export interface StringLiteral extends TSESTree.Literal {
  value: string;
}

type StringNode = StringLiteral | TSESTree.TemplateLiteral;

/**
 * Checks if the given `node` is a {@link StringLiteral}.
 *
 * @param {Node} node
 *
 * @return {node is StringLiteral}
 */
export const isStringLiteral = (node: TSESTree.Node): node is StringLiteral =>
  node.type === AST_NODE_TYPES.Literal && typeof node.value === 'string';

export const isTemplateLiteral = (
  node: TSESTree.Node,
): node is TSESTree.TemplateLiteral =>
  node.type === AST_NODE_TYPES.TemplateLiteral;

/**
 * Checks if the given `node` is a {@link StringNode}.
 *
 * @param {Node} node
 *
 * @return {node is StringNode}
 */
export const isStringNode = (
  node: TSESTree.Node | undefined,
): node is StringNode =>
  node !== undefined && (isStringLiteral(node) || isTemplateLiteral(node));

/**
 * A `Literal` with a specific string-type `value` - i.e `'expect'`.
 */
interface SpecificStringLiteral<Value extends string> extends StringLiteral {
  value: Value;
}

/**
 * Checks if the given `node` is a `StringLiteral` with the given `value`.
 *
 * @param {Node} node
 * @param {V} value
 *
 * @return {node is SpecificStringLiteral<V>}
 *
 * @template {V}.
 */
const isSpecificStringLiteral = <V extends string>(
  node: TSESTree.Node,
  value: V,
): node is SpecificStringLiteral<V> =>
  isStringLiteral(node) && node.value === value;

interface SpecificTemplateLiteral<Value extends string>
  extends TSESTree.TemplateLiteral {
  quasis: [TSESTree.TemplateElement & { value: { raw: Value; cooked: Value } }];
}

/**
 * Checks if the given `node` is a `TemplateLiteral` with the given `value`.
 *
 * Complex `TemplateLiteral`s are not considered specific, and so will return `false`.
 *
 * @param {Node} node
 * @param {V} value
 *
 * @return {node is SpecificTemplateLiteral<V>}
 *
 * @template V
 */
const isSpecificTemplateLiteral = <V extends string>(
  node: TSESTree.Node,
  value: V,
): node is SpecificTemplateLiteral<V> =>
  isTemplateLiteral(node) &&
  node.quasis.length === 1 && // bail out if not simple
  node.quasis[0].value.raw === value;

type SpecificStringNode<S extends string> =
  | SpecificStringLiteral<S>
  | SpecificTemplateLiteral<S>;

const isSpecificStringNode = <V extends string>(
  node: TSESTree.Node,
  specifics: V,
): node is SpecificStringNode<V> =>
  isSpecificStringLiteral(node, specifics) ||
  isSpecificTemplateLiteral(node, specifics);

const getSpecificStringValue = <S extends string>(
  arg: SpecificStringNode<S>,
): S => (isTemplateLiteral(arg) ? arg.quasis[0].value.raw : arg.value);

/**
 * Represents a `MemberExpression` with a "known" `property`.
 */
export interface KnownMemberExpression<Name extends string = string>
  extends TSESTree.MemberExpression {
  property: SpecificAccessorExpression<Name>;
}

/**
 * Represents a `CallExpression` with a "known" `property` accessor.
 *
 * i.e `KnownCallExpression<'includes'>` represents `.includes()`.
 */
export interface KnownCallExpression<Name extends string = string>
  extends TSESTree.CallExpression {
  callee: CalledKnownMemberExpression<Name>;
}

/**
 * Represents a `MemberExpression` with a "known" `property`, that is called.
 *
 * This is `KnownCallExpression` from the perspective of the `MemberExpression` node.
 */
export interface CalledKnownMemberExpression<Name extends string = string>
  extends KnownMemberExpression<Name> {
  parent: KnownCallExpression<Name>;
}

/**
 * An `Identifier` with a specific `name` - i.e `expect`.
 */
export interface SpecificIdentifier<Name extends string>
  extends TSESTree.Identifier {
  name: Name;
}

/**
 * Checks if the given `node` is an `Identifier` with the specific `name`.
 *
 * @param {Node} node
 * @param {V} name
 *
 * @return {node is SpecificIdentifier<Name>}
 *
 * @template V
 */
const isSpecificIdentifier = <V extends string>(
  node: TSESTree.Node,
  name: V,
): node is SpecificIdentifier<V> =>
  node.type === AST_NODE_TYPES.Identifier && node.name === name;

type AccessorNode = SpecificAccessorExpression<string>;

export const isSupportedAccessor = (
  node: TSESTree.Node,
): node is AccessorNode =>
  node.type === AST_NODE_TYPES.Identifier || isStringNode(node);

export const getAccessorValue = <S extends string = string>(
  accessor: SpecificAccessorExpression<S>,
): S =>
  accessor.type === AST_NODE_TYPES.Identifier
    ? accessor.name
    : getSpecificStringValue(accessor);

/**
 * Checks if the given `node` is an `AccessorExpression` with the specific `value`.
 *
 * @param {Node} node
 * @param {V} accessor
 *
 * @return {node is SpecificAccessorExpression<V>}
 *
 * @template V
 */
export const isSpecificAccessorExpression = <V extends string>(
  node: TSESTree.Node,
  accessor: V,
): node is SpecificAccessorExpression<V> =>
  isSpecificIdentifier(node, accessor) || isSpecificStringNode(node, accessor);

export interface ValidExpectCall<
  Argument extends TSESTree.Expression = TSESTree.Expression
> extends ExpectCall {
  arguments: [Argument];
}

export interface CallExpressionWithSingleArgument<
  Argument extends TSESTree.Expression = TSESTree.Expression
> extends TSESTree.CallExpression {
  arguments: [Argument];
}

export const hasOneArgument = (
  node: TSESTree.CallExpression,
): node is CallExpressionWithSingleArgument =>
  node.arguments && node.arguments.length === 1;

/**
 * An `Identifier` with a specific `name` - i.e `expect`.
 */
export interface SpecificIdentifier<Name extends string>
  extends TSESTree.Identifier {
  name: Name;
}

type SpecificAccessorExpression<Specifics extends string> =
  | SpecificStringNode<Specifics>
  | SpecificIdentifier<Specifics>;

type ExpectAccessor = SpecificAccessorExpression<'expect'>;

export const isExpectAccessor = (node: TSESTree.Node): node is ExpectAccessor =>
  isSpecificAccessorExpression(node, 'expect');

export interface ExpectCall extends TSESTree.CallExpression {
  callee: SpecificAccessorExpression<'expect'>;
  parent: TSESTree.Node;
}

/**
 * Checks if the given `node` is a valid `ExpectCall`.
 *
 * In order to be an `ExpectCall`, the `node` must:
 *  * be a `CallExpression`,
 *  * have an accessor named 'expect',
 *  * have a `parent`.
 *
 * @param {Node} node
 *
 * @return {node is ExpectCall}
 */
export const isExpectCall = (node: TSESTree.Node): node is ExpectCall =>
  node.type === AST_NODE_TYPES.CallExpression &&
  isExpectAccessor(node.callee) &&
  node.parent !== undefined;

/**
 * Checks if the given `node` is a valid `ExpectCall`.
 *
 * In order to be an `ExpectCall`, the `node` must:
 *  * be a `CallExpression`,
 *  * have an accessor named 'expect',
 *  * have only *one* argument, and
 *  * have a `parent`.
 *
 * @param {Node} node
 *
 * @return {node is ExpectCall}
 */
export const isValidExpectCall = (
  node: TSESTree.Node,
): node is ValidExpectCall =>
  isExpectCall(node) && hasOneArgument(node) && node.parent !== undefined;

/**
 * Represents a `MemberExpression` that comes after an `ExpectCall`.
 */
export interface ExpectMember<
  PropertyName extends ExpectPropertyName = ExpectPropertyName,
  Parent extends TSESTree.Node | undefined = TSESTree.Node | undefined
> extends KnownMemberExpression<PropertyName> {
  object: ExpectCall | ExpectMember;
  parent: Parent;
}

export const isExpectMember = <
  Name extends ExpectPropertyName = ExpectPropertyName
>(
  node: TSESTree.Node,
  name?: Name,
): node is ExpectMember<Name> =>
  node.type === AST_NODE_TYPES.MemberExpression &&
  isSupportedAccessor(node.property) &&
  (name === undefined || getAccessorValue(node.property) === name);

/**
 * Represents all the jest matchers.
 */
export type MatcherName = string /* & not ModifierName */;
export type ExpectPropertyName = ModifierName | MatcherName;

export type ParsedEqualityMatcherCall<
  Argument extends TSESTree.Expression = TSESTree.Expression
> = Omit<ParsedExpectMatcher<EqualityMatcher>, 'arguments'> & {
  // todo: probs should also type node parent as CallExpression
  arguments: [Argument];
};

export const isParsedEqualityMatcherCall = (
  matcher: ParsedExpectMatcher,
): matcher is ParsedEqualityMatcherCall =>
  EqualityMatcher.hasOwnProperty(matcher.name) &&
  matcher.arguments !== null &&
  matcher.arguments.length === 1;

export enum EqualityMatcher {
  toBe = 'toBe',
  toEqual = 'toEqual',
}

export enum ModifierName {
  not = 'not',
  rejects = 'rejects',
  resolves = 'resolves',
}

interface ParsedExpectMember<
  Name extends ExpectPropertyName = ExpectPropertyName,
  Node extends ExpectMember<Name> = ExpectMember<Name>
> {
  name: Name;
  node: Node;
}

export interface ParsedExpectMatcher<
  Matcher extends MatcherName = MatcherName,
  Node extends ExpectMember<Matcher> = ExpectMember<Matcher>
> extends ParsedExpectMember<Matcher, Node> {
  arguments: TSESTree.CallExpression['arguments'] | null;
  // isNamed<PossibleName extends Matcher>(
  //   name: PossibleName,
  //   ...or: PossibleName[]
  // ): this is ParsedExpectMatcher<PossibleName>;
  // isNamed<PossibleName extends Matcher>(
  //   // name: PossibleName,
  //   ...names: [PossibleName, ...PossibleName[]]
  // ): this is ParsedExpectMatcher<PossibleName, Node>;
}

type BaseParsedModifier<
  Modifier extends ModifierName = ModifierName
> = ParsedExpectMember<Modifier>;

type NegatableModifierName = ModifierName.rejects | ModifierName.resolves;
type NotNegatableModifierName = ModifierName.not;

interface NegatableParsedModifier<
  Modifier extends NegatableModifierName = NegatableModifierName
> extends BaseParsedModifier<Modifier> {
  negation?: ExpectMember<ModifierName.not>;
}

export interface NotNegatableParsedModifier<
  Modifier extends NotNegatableModifierName = NotNegatableModifierName
> extends BaseParsedModifier<Modifier> {
  negation?: never;
}

type ParsedExpectModifier =
  | NotNegatableParsedModifier<NotNegatableModifierName>
  | NegatableParsedModifier<NegatableModifierName>;

interface Expectation<ExpectNode extends ExpectCall = ValidExpectCall> {
  expect: ExpectNode;
  /** @deprecated */
  expectCall: ExpectNode;
  modifier?: ParsedExpectModifier;
  matcher?: ParsedExpectMatcher;
}

const parseExpectMember = <S extends ExpectPropertyName>(
  expectMember: ExpectMember<S>,
): ParsedExpectMember<S> => ({
  name: getAccessorValue<S>(expectMember.property),
  node: expectMember,
});

const reparseAsMatcher = (
  parsedMember: ParsedExpectMember,
): ParsedExpectMatcher => ({
  ...parsedMember,
  /**
   * The arguments being passed to this `Matcher`, if any.
   *
   * If this matcher isn't called, this will be `null`.
   */
  arguments:
    parsedMember.node.parent &&
    parsedMember.node.parent.type === AST_NODE_TYPES.CallExpression
      ? parsedMember.node.parent.arguments
      : null,
  // isNamed(...names: string[]) {
  //   return names.includes(this.name);
  // },
});

/**
 * Re-parses the given `parsedMember` as a `ParsedExpectModifier`.
 *
 * If the given `parsedMember` does not have a `name` of a valid `Modifier`,
 * an exception will be thrown.
 *
 * @param {ParsedExpectMember<ModifierName>} parsedMember
 *
 * @return {ParsedExpectModifier}
 */
const reparseMemberAsModifier = (
  parsedMember: ParsedExpectMember<ModifierName>,
): ParsedExpectModifier => {
  if (isSpecificMember(parsedMember, ModifierName.not)) {
    return parsedMember;
  }

  /* istanbul ignore next */
  if (
    !(
      isSpecificMember(parsedMember, ModifierName.resolves) ||
      isSpecificMember(parsedMember, ModifierName.rejects)
    )
  ) {
    throw new Error(
      `modifier name must be either "${ModifierName.resolves}" or "${ModifierName.rejects}" (got "${parsedMember.name}")`,
    ); // ts doesn't think that the ModifierName.not check is the direct inverse as the above two checks
  } // todo: impossible at runtime, but can't be typed w/o negation support

  const negation =
    parsedMember.node.parent &&
    isExpectMember(parsedMember.node.parent, ModifierName.not)
      ? parsedMember.node.parent
      : undefined;

  return {
    ...parsedMember,
    negation,
  };
};

const isSpecificMember = <Name extends ExpectPropertyName>(
  member: ParsedExpectMember,
  specific: Name,
): member is ParsedExpectMember<Name> => member.name === specific;

/**
 * Checks if the given `ParsedExpectMember` should be re-parsed as an `ParsedExpectModifier`.
 *
 * @param {ParsedExpectMember} member
 *
 * @return {member is ParsedExpectMember<ModifierName>}
 */
const shouldBeParsedExpectModifier = (
  member: ParsedExpectMember,
): member is ParsedExpectMember<ModifierName> =>
  ModifierName.hasOwnProperty(member.name);

export const parseExpectCall = <ExpectNode extends ExpectCall>(
  expectCall: ExpectNode,
): Expectation<ExpectNode> => {
  const expectation: Expectation<ExpectNode> = {
    expect: expectCall,
    expectCall,
  };

  if (!isExpectMember(expectCall.parent)) {
    return expectation;
  }

  const parsedMember = parseExpectMember(expectCall.parent);
  if (!shouldBeParsedExpectModifier(parsedMember)) {
    expectation.matcher = reparseAsMatcher(parsedMember);

    return expectation;
  }

  const modifier = (expectation.modifier = reparseMemberAsModifier(
    parsedMember,
  ));

  const memberNode =
    ('negation' in modifier && modifier.negation) || modifier.node;

  if (!memberNode.parent || !isExpectMember(memberNode.parent)) {
    return expectation;
  }

  expectation.matcher = reparseAsMatcher(parseExpectMember(memberNode.parent));

  return expectation;
};

export enum DescribeAlias {
  'describe' = 'describe',
  'fdescribe' = 'fdescribe',
  'xdescribe' = 'xdescribe',
}

export enum TestCaseName {
  'fit' = 'fit',
  'it' = 'it',
  'test' = 'test',
  'xit' = 'xit',
  'xtest' = 'xtest',
}

export enum HookName {
  'beforeAll' = 'beforeAll',
  'beforeEach' = 'beforeEach',
  'afterAll' = 'afterAll',
  'afterEach' = 'afterEach',
}

export enum DescribeProperty {
  'each' = 'each',
  'only' = 'only',
  'skip' = 'skip',
}

export enum TestCaseProperty {
  'each' = 'each',
  'only' = 'only',
  'skip' = 'skip',
  'todo' = 'todo',
}

export type JestFunctionName = DescribeAlias | TestCaseName | HookName;

export interface JestFunctionIdentifier<FunctionName extends JestFunctionName>
  extends TSESTree.Identifier {
  name: FunctionName;
}

export interface JestFunctionMemberExpression<
  FunctionName extends JestFunctionName
> extends TSESTree.MemberExpression {
  object: JestFunctionIdentifier<FunctionName>;
}

export interface JestFunctionCallExpressionWithMemberExpressionCallee<
  FunctionName extends JestFunctionName
> extends TSESTree.CallExpression {
  callee: JestFunctionMemberExpression<FunctionName>;
}

export interface JestFunctionCallExpressionWithIdentifierCallee<
  FunctionName extends JestFunctionName
> extends TSESTree.CallExpression {
  callee: JestFunctionIdentifier<FunctionName>;
}

export type JestFunctionCallExpression<
  FunctionName extends JestFunctionName = JestFunctionName
> =
  | JestFunctionCallExpressionWithMemberExpressionCallee<FunctionName>
  | JestFunctionCallExpressionWithIdentifierCallee<FunctionName>;

export function getNodeName(
  node:
    | JestFunctionMemberExpression<JestFunctionName>
    | JestFunctionIdentifier<JestFunctionName>,
): string;
export function getNodeName(node: TSESTree.Node): string | null;
export function getNodeName(node: TSESTree.Node): string | null {
  function joinNames(a?: string | null, b?: string | null): string | null {
    return a && b ? `${a}.${b}` : null;
  }

  switch (node.type) {
    case AST_NODE_TYPES.Identifier:
      return node.name;
    case AST_NODE_TYPES.Literal:
      return `${node.value}`;
    case AST_NODE_TYPES.TemplateLiteral:
      if (node.expressions.length === 0) return node.quasis[0].value.cooked;
      break;
    case AST_NODE_TYPES.MemberExpression:
      return joinNames(getNodeName(node.object), getNodeName(node.property));
  }

  return null;
}

export type FunctionExpression =
  | TSESTree.ArrowFunctionExpression
  | TSESTree.FunctionExpression;

export const isFunction = (node: TSESTree.Node): node is FunctionExpression =>
  node.type === AST_NODE_TYPES.FunctionExpression ||
  node.type === AST_NODE_TYPES.ArrowFunctionExpression;

export const isHook = (
  node: TSESTree.CallExpression,
): node is JestFunctionCallExpressionWithIdentifierCallee<HookName> => {
  return (
    node.callee.type === AST_NODE_TYPES.Identifier &&
    HookName.hasOwnProperty(node.callee.name)
  );
};

export const isTestCase = (
  node: TSESTree.CallExpression,
): node is JestFunctionCallExpression<TestCaseName> => {
  return (
    (node.callee.type === AST_NODE_TYPES.Identifier &&
      TestCaseName.hasOwnProperty(node.callee.name)) ||
    (node.callee.type === AST_NODE_TYPES.MemberExpression &&
      node.callee.object.type === AST_NODE_TYPES.Identifier &&
      TestCaseName.hasOwnProperty(node.callee.object.name) &&
      node.callee.property.type === AST_NODE_TYPES.Identifier &&
      TestCaseProperty.hasOwnProperty(node.callee.property.name))
  );
};

export const isDescribe = (
  node: TSESTree.CallExpression,
): node is JestFunctionCallExpression<DescribeAlias> => {
  return (
    (node.callee.type === AST_NODE_TYPES.Identifier &&
      DescribeAlias.hasOwnProperty(node.callee.name)) ||
    (node.callee.type === AST_NODE_TYPES.MemberExpression &&
      node.callee.object.type === AST_NODE_TYPES.Identifier &&
      DescribeAlias.hasOwnProperty(node.callee.object.name) &&
      node.callee.property.type === AST_NODE_TYPES.Identifier &&
      DescribeProperty.hasOwnProperty(node.callee.property.name))
  );
};

export const isLiteralNode = (node: {
  type: AST_NODE_TYPES;
}): node is TSESTree.Literal => node.type === AST_NODE_TYPES.Literal;

export const hasExpressions = (
  node: TSESTree.Node,
): node is TSESTree.Expression =>
  'expressions' in node && node.expressions.length > 0;

/* istanbul ignore next we'll need this later */
export const getStringValue = (arg: StringNode): string =>
  isTemplateLiteral(arg) ? arg.quasis[0].value.raw : arg.value;

const collectReferences = (scope: TSESLint.Scope.Scope) => {
  const locals = new Set();
  const unresolved = new Set();

  let currentScope: TSESLint.Scope.Scope | null = scope;

  while (currentScope !== null) {
    for (const ref of currentScope.variables) {
      const isReferenceDefined = ref.defs.some(def => {
        return def.type !== 'ImplicitGlobalVariable';
      });

      if (isReferenceDefined) {
        locals.add(ref.name);
      }
    }

    for (const ref of currentScope.through) {
      unresolved.add(ref.identifier.name);
    }

    currentScope = currentScope.upper;
  }

  return { locals, unresolved };
};

export const scopeHasLocalReference = (
  scope: TSESLint.Scope.Scope,
  referenceName: string,
) => {
  const references = collectReferences(scope);
  return (
    // referenceName was found as a local variable or function declaration.
    references.locals.has(referenceName) ||
    // referenceName was not found as an unresolved reference,
    // meaning it is likely not an implicit global reference.
    !references.unresolved.has(referenceName)
  );
};
