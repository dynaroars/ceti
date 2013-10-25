def get_assertions(fname, in_outs, common_ins):
    """
    sage: get_assertions('add',[((1,2),3),((3,4),7)])
    'if(add(1,2) == 3 && add(3,4) == 7)'
    """
    assertions = ["{}({}) == {}"
                  .format(fname, ','.join(map(str,list(i)+common_ins)), o)
                  for (i,o) in in_outs]
    assertions = ' && '.join(assertions)
    return "if({})".format(assertions)
