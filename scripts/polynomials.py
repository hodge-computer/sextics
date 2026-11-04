"""Parse the exact polynomial expressions used by mathematical records."""
import ast


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exact_polynomial(expression, variables):
    """Parse data without eval, sympify(string), or executable parser transformations."""
    import sympy as s
    names=dict(zip(('X0','X1','X2','Y0','Y1','Y2'),variables))
    def visit(node):
        if isinstance(node,ast.Constant) and type(node.value) is int: return s.Integer(node.value)
        if isinstance(node,ast.Name) and node.id in names: return names[node.id]
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub): return -visit(node.operand)
        if isinstance(node,ast.BinOp):
            if isinstance(node.op,ast.Pow):
                require(isinstance(node.right,ast.Constant) and type(node.right.value) is int and node.right.value>=0,'Invalid power')
                return visit(node.left)**node.right.value
            if isinstance(node.op,ast.Div):
                require(isinstance(node.right,ast.Constant) and type(node.right.value) is int and node.right.value>0,'Invalid denominator')
                return visit(node.left)/node.right.value
            if isinstance(node.op,ast.Add): return visit(node.left)+visit(node.right)
            if isinstance(node.op,ast.Sub): return visit(node.left)-visit(node.right)
            if isinstance(node.op,ast.Mult): return visit(node.left)*visit(node.right)
        raise ValueError('Invalid exact polynomial expression')
    return visit(ast.parse(expression,mode='eval').body)

