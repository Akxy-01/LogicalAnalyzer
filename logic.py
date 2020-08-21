import re
import copy

def read_input():
    input_handle = open("input.txt", "r")
    input_config = {}
    input_file_contents = input_handle.readlines()
    queries = []
    number_of_queries = int(input_file_contents[0])
    for i in range(number_of_queries):
        queries.append(input_file_contents[1+i].rstrip())
    input_config['queries'] = queries
    kb = {}
    for i in range(int(input_file_contents[number_of_queries+1])):
        kb[i] = input_file_contents[number_of_queries+2+i].rstrip().replace(' ', '')
    input_config['kb'] = kb
    return input_config


def write_output(final_result):
    file_out = open("output.txt", "w")
    newline = ''
    for query_result in final_result:
        file_out.write(newline+str(query_result).upper())
        newline = '\n'


def pre_process_input(input_config):
    predicates = {}
    constants = []
    variables = {}
    for key, value in input_config['kb'].items():
        if value.find('=>') != -1:
            final_kb = []
            cnf_predicates = value.split('=>')
            if cnf_predicates[0].find('&') != -1:
                left_predicates = cnf_predicates[0].split('&')
                for each in left_predicates:
                    if each[0] == '~':
                        final_kb.append(each[1:])
                    else:
                        final_kb.append('~' + each)
            else:
                if cnf_predicates[0][0] == '~':
                    final_kb.append(cnf_predicates[0][1:])
                else:
                    final_kb.append('~' + cnf_predicates[0])
            final_kb.append(cnf_predicates[1])
            input_config['kb'][key] = '|'.join(final_kb)
            for each in re.split(r'[|&]', input_config['kb'][key]):
                predicate, arguments = each.replace(')', '').replace('\n', '').split('(')
                if predicate not in predicates:
                    predicates[predicate] = [key]
                elif key not in predicates[predicate]:
                    predicates[predicate].append(key)
                for each_argument in arguments.split(','):
                    if each_argument[0].islower():
                        if each_argument[0] not in variables.keys():
                            variables[each_argument] = None
                    else:
                        if each_argument not in constants:
                            constants.append(each_argument)
        else:
            for each in re.split(r'[|&]', input_config['kb'][key]):
                predicate, arguments = each.replace(')', '').replace('\n', '').split('(')
                if predicate not in predicates:
                    predicates[predicate] = [key]
                elif key not in predicates[predicate]:
                    predicates[predicate].append(key)
                for each_argument in arguments.split(','):
                    if each_argument[0].islower():
                        if each_argument[0] not in variables.keys():
                            variables[each_argument] = None
                    else:
                        if each_argument not in constants:
                            constants.append(each_argument)
    return predicates, constants, variables


def substitution(predicate, variables, to_be_substituted_variables):
    new_predicate = predicate.split('(')[0] + '('
    arguments = predicate.replace(')', '').split('(')[1].split(',')
    for each_argument in arguments:
        if each_argument in to_be_substituted_variables:
            new_predicate = new_predicate + variables[each_argument] + ','
        else:
            new_predicate = new_predicate + each_argument + ','
    new_predicate = new_predicate[:-1] + ')'
    return new_predicate


def unify(predicate_1, predicate_2, variables, constants, variables_to_be_substituted):
    predicate_1_arguments = predicate_1.replace(')', '').split('(')[1].split(',')
    predicate_2_arguments = predicate_2.replace(')', '').split('(')[1].split(',')
    flag = False
    visited = []
    for index, each in enumerate(predicate_1_arguments):
        if (each in constants or each[0].isupper()) and (predicate_2_arguments[index] in constants or predicate_2_arguments[index][0].isupper()):
            if each != predicate_2_arguments[index]:
                return False
            else:
                flag = True

        elif (each in constants or each[0].isupper()) and predicate_2_arguments[index].islower():
            if predicate_2_arguments[index] in visited and variables[predicate_2_arguments[index]]:
                if variables[predicate_2_arguments[index]] == each:
                    flag = True
                else:
                    return False
            else:
                flag = True
                variables[predicate_2_arguments[index]] = each
                variables_to_be_substituted.append(predicate_2_arguments[index])

        elif each.islower() and (predicate_2_arguments[index] in constants or predicate_2_arguments[index][0].isupper()):
            if each in visited and variables[each]:
                if variables[each] == predicate_2_arguments[index]:
                    variables_to_be_substituted.append(each)
                    flag = True
                else:
                    return False
            else:
                flag = True
                variables[each] = predicate_2_arguments[index]
                variables_to_be_substituted.append(each)

        elif (each in variables.keys() or each[0].islower()) and (predicate_2_arguments[index] in variables.keys() or predicate_2_arguments[index][0].islower()):
            if each != predicate_2_arguments[index]:
                variables[each] = predicate_2_arguments[index]
                variables_to_be_substituted.append(each)
            flag = True

        visited.append(each)
        visited.append(predicate_2_arguments[index])
    return flag


def res(config, partial_query, predicates, constants, variables, visited, whole_query):
    if partial_query[0] == '~':
        partial_query = partial_query[1:]
    else:
        partial_query = '~' + partial_query

    copy_whole = whole_query[:]
    copy_visited = visited[:]
    predicate_name_of_partial_query = partial_query.split('(')[0]
    if predicate_name_of_partial_query in predicates.keys():
        search_statements = predicates[predicate_name_of_partial_query]
        for every_search_statement in search_statements:
            single_predicate_flag = False
            whole_query = copy_whole[:]
            visited = copy_visited[:]
            if visited[every_search_statement]:
                continue
            kb_statement = config['kb'][every_search_statement]
            kb_predicate = None
            temp_query = []
            enum_predicates = re.split(r'[|&]+', kb_statement)
            if len(enum_predicates) == 1:
                args = enum_predicates[0].replace(')', '').split('(')[1].split(',')
                arg_flag = True
                for j in args:
                    if not j[0].isupper():
                        arg_flag = False  # put break after this
                if arg_flag:
                    single_predicate_flag = True
            for e in enum_predicates:
                if e.split('(')[0] == predicate_name_of_partial_query:
                    kb_predicate = e
                    temp_query.append(e)
                else:
                    temp_query.append(e)
            variables_to_substitue = []
            if unify(kb_predicate, partial_query, variables, constants, variables_to_substitue):
                original_partial_query = '~' + partial_query if partial_query[0] != '~' else partial_query[1:]
                g_query = []
                if whole_query:
                    g_query = whole_query[:]
                for x in g_query:
                    if x == original_partial_query:
                        continue
                    substituted_query = substitution(x, variables, variables_to_substitue)
                    whole_query.remove(x)
                    whole_query.append(substituted_query)

                for j in temp_query:
                    if j == kb_predicate:
                        continue
                    substituted_query = substitution(j, variables, variables_to_substitue)
                    whole_query.append(substituted_query)

                if not single_predicate_flag:
                    visited[every_search_statement] = True

                if original_partial_query in whole_query:
                    whole_query.remove(original_partial_query)
                if not whole_query:
                    return True
                predicate_index = 0
                while predicate_index < len(whole_query):
                    next_predicate_to_be_resolved = whole_query[predicate_index]
                    if res(config, next_predicate_to_be_resolved, predicates, constants, variables, visited, whole_query):
                        return True
                    else:
                        predicate_index += 1
        return False
    else:
        return False


if __name__ == "__main__":
    config = read_input()
    predicates, constants, variables = pre_process_input(config)
    result = [False] * len(config['queries'])
    i = 0
    for every_query in config['queries']:
        negated_query = ('~' + every_query) if every_query[0] != '~' else every_query[1:]
        visited = [False] * len(config['kb'].keys())
        variables_copy = copy.deepcopy(variables)
        whole_query = []
        if res(config, negated_query, predicates, constants, variables_copy, visited, whole_query):
            result[i] = True
        i += 1
    write_output(result)

