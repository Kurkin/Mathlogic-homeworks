#include <iostream>
#include <cmath>
#include <algorithm>
#include <string>
#include <cstdio>
#include <vector>
#include <queue>
#include <set>
#include <stdexcept>
#include <fstream>

using namespace std;

vector <string> strings;
set <string> need_for_MP;
vector <int> prove;
string s;
int num = 1;

struct node
{
    char operation;
    string value;
    node *left;
    node *right;
    node *parent;
};

bool is_operation(char c)
{
    return ((c == '-') || (c == '&') || (c == '|') || (c == '!'));
}

bool is_ident(char c)
{
    return (!is_operation(c) && (c != '(') && c != ')');
}

int operation_priority(char c)
{
    if (c == '-')
    {
        return 1;
    }
    else if (c == '|')
    {
        return 2;
    }
    else if (c == '&')
    {
        return 3;
    }
    else if (c == '!')
    {
        return 4;
    }
}

bool left_associative(char c)
{
    return ((c == '&') || (c == '|'));
}

string to_normal_string(string expr)
{
    string new_expr = "";
    for (int i = 0; i < expr.size(); i++)
    {
        if (expr[i] != ' ' && expr[i] != '>')
        {
            new_expr += expr[i];
        }
    }
    return new_expr;
}

string delete_spaces(string old_string)
{
    string new_string = "";
    for (int i = 0; i < old_string.size(); i++)
    {
        if (old_string[i] != ' ')
        {
            new_string += old_string[i];
        }
    }
    return new_string;
}

vector <string> to_stack(string input)
{
    vector <string> stack_ident;
    vector <char> stack_operation;
    for (int i = 0; i < input.size(); i++)
    {
        char c = input[i];
        if (is_ident(c))
        {
            string s;
            while (is_ident(input[i]) && i < input.size())
            {
                s += input[i];
                i++;
            }
            i--;
            stack_ident.push_back(s);
        }
        else if (is_operation(c))
        {
            bool flag = true;
            while (flag && stack_operation.size() != 0)
            {
                char sc = stack_operation.back();
                if (sc != '(' && (left_associative(c) && (operation_priority(c) <= operation_priority(sc)) || (!left_associative(c) && (operation_priority(c) < operation_priority(sc)))))
                {
                    string str = "";
                    str += sc;
                    stack_ident.push_back(str);
                    stack_operation.pop_back();
                }
                else
                {
                    flag = false;
                }
            }
            stack_operation.push_back(c);
        }
        else if (c == '(')
        {
            stack_operation.push_back(c);
        }
        else if (c == ')')
        {
            bool flag = true;
            while (flag && stack_operation.size() != 0)
            {
                char sc = stack_operation.back();
                if (sc == '(')
                {
                    flag = false;
                }
                else
                {
                    string str = "";
                    str += sc;
                    stack_ident.push_back(str);
                    stack_operation.pop_back();
                }
            }
            stack_operation.pop_back();
        }
    }
    while (stack_operation.size() != 0)
    {
        char sc = stack_operation.back();
        string str = "";
        str += sc;
        stack_ident.push_back(str);
        stack_operation.pop_back();
    }
    return stack_ident;
}

node* to_tree (vector <string> expr)
{
    reverse(expr.begin(), expr.end());
    node *tree = new node;
    tree -> parent = NULL;
    tree -> left = NULL;
    tree -> right = NULL;
    while (expr.size() != 0)
    {
        string str = expr.back();
        expr.pop_back();
        char c = str[0];
        if (is_ident(c))
        {
            if (expr.size() == 0)
            {
                tree -> value = str;
            }
            else if (tree -> right == NULL && tree -> left == NULL)
            {
                tree -> left = new node;
                tree -> left -> parent = tree;
                tree -> left -> left = NULL;
                tree -> left -> right = NULL;
                tree -> left -> value = str;
            }
            else
            if (tree -> right == NULL)
            {
                tree -> right = new node;
                tree -> right -> parent = tree;
                tree -> right -> left = NULL;
                tree -> right -> right = NULL;
                tree -> right -> value = str;
            }
            else if (tree -> left != NULL && tree -> right != NULL)
            {
                node *tmp = new node;
                tmp -> left = tree -> right;
                tmp -> parent = tree;
                tmp -> left -> parent = tmp;
                tree -> right = tmp;
                tmp -> right = new node;
                tmp -> right -> left = NULL;
                tmp -> right -> right = NULL;
                tmp -> right -> parent = tmp;
                tmp -> right -> value = str;
                tree = tmp;
            }
        }
        else if (is_operation(c))
        {
            tree -> operation = c;
            if (c == '!')
            {
                if (tree -> right != NULL && tree -> left != NULL)
                {
                    node *tmp = new node;
                    tmp -> left = tree -> right;
                    tmp -> right = NULL;
                    tmp -> parent = tree;
                    tree -> right = tmp;
                    tmp -> value = str + "(" + tmp -> left -> value + ")";
                    tmp -> operation = '!';
                    continue;
                }
                tree -> value = str + "(" + tree -> left -> value + ")";
            }
            else
            {
                tree -> value = "(" + tree -> left -> value + ")" + str;
                if (tree -> right != NULL)
                {
                    tree -> value += "(" + tree -> right -> value + ")";
                }
            }
            if (tree -> parent != NULL)
            {
                tree = tree -> parent;
            }
            else if (expr.size() != 0)
            {
                tree -> parent = new node;
                tree -> parent -> left = tree;
                tree = tree -> parent;
                tree -> right = NULL;
                tree -> parent = NULL;
            }
            else if (expr.size() == 0) {}
        }
    }
    return tree;
}

int main()
{
    ifstream in("deduction.in");
    ofstream out("deduction.out");
    bool fl = true;
    vector <node*> trees;
    node *tree_last;
    int n = 0;
    string last = "";
    while (getline(in, s))
    {
        if (fl)
        {
            s = delete_spaces(s);
            int j = 0;
            int k = 0;
            while (s[j] != '|' || s[j + 1] != '-')
            {
                while (s[j] != ',' && (s[j] != '|' || s[j + 1] != '-'))
                {
                    j++;
                }
                strings.push_back(s.substr(k, j - k));
                n++;
                if (s[j] == '|')
                {
                    string s1 = s.substr(j + 2, s.size() - j - 2);
                    int tmp = strings.size() - 2;
                    for (int i = 0; i < tmp; i++)
                    {
                        out << strings[i] << ", ";
                    }
                    if (strings.size() >= 2)
                    {
                        out << strings[strings.size() - 2] << "|-" << "(" << strings[strings.size() - 1] << ")->(" << s1 << ")" << endl;
                        last = strings[strings.size() - 1];
                        tree_last = to_tree(to_stack(to_normal_string(last)));
                    }
                    else
                    {
                        out << "|-" << "(" << strings[strings.size() - 1] << ")->(" << s1 << ")" << endl;
                        last = strings[strings.size() - 1];
                        tree_last = to_tree(to_stack(to_normal_string(last)));
                    }
                    strings.pop_back();
                    n--;
                    break;
                }
                k = j + 1;
                j++;
            }
            fl = false;
        }
        else
        {
            strings.push_back(s);
        }
        prove.push_back(-1);
    }
    trees.resize(strings.size());
    for (int i = n; i < strings.size(); i++)
    {
        bool flag = true;
        strings[i] = delete_spaces(strings[i]);
        trees[i] = to_tree(to_stack(to_normal_string(strings[i])));
        if (trees[i] -> operation == '-')
        {
            if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> right -> right != NULL
                    && trees[i] -> left -> value == trees[i] -> right -> right -> value && trees[i] -> right -> operation == '-')
            {
                out << strings[i] << endl;
                out << "(" << strings[i] << ")->" << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                out << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                num += 3;
                prove[i] = num - 1;
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> left -> left != NULL && trees[i] -> right -> left != NULL && trees[i] -> right -> left -> left != NULL
                    && trees[i] -> left -> right != NULL && trees[i] -> right -> left -> right != NULL && trees[i] -> right -> left -> right -> left != NULL
                    && trees[i] -> right -> left -> right -> right != NULL && trees[i] -> right -> right != NULL && trees[i] -> right -> right -> right != NULL
                    && trees[i] -> right -> right -> left != NULL
                    && trees[i] -> left -> left -> value == trees[i] -> right -> left -> left -> value
                    && trees[i] -> left -> right -> value == trees[i] -> right -> left -> right -> left -> value
                    && trees[i] -> right -> left -> right -> right -> value == trees[i] -> right -> right -> right -> value
                    && trees[i] -> left -> left -> value == trees[i] -> right -> right -> left -> value
                    && trees[i] -> left -> operation == '-' && trees[i] -> right -> operation == '-' && trees[i] -> right -> left -> operation == '-'
                    && trees[i] -> right -> left -> right -> operation == '-' && trees[i] -> right -> right -> operation == '-')
            {
                out << strings[i] << endl;
                out << "(" << strings[i] << ")->" << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                out << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                num += 3;
                prove[i] = num - 1;
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> right -> left != NULL && trees[i] -> right -> right != NULL
                    && trees[i] -> right -> right -> left != NULL && trees[i] -> right -> right -> right != NULL
                    && trees[i] -> left -> value == trees[i] -> right -> right -> left -> value && trees[i] -> right -> left -> value == trees[i] -> right -> right -> right -> value
                    && trees[i] -> right -> operation == '-' && trees[i] -> right -> right -> operation == '&')
            {
                out << strings[i] << endl;
                out << "(" << strings[i] << ")->" << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                out << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                num += 3;
                prove[i] = num - 1;
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> left -> left != NULL && trees[i] -> left -> right != NULL
                    && trees[i] -> left -> left -> value == trees[i] -> right -> value && trees[i] -> left -> operation == '&')
            {
                out << strings[i] << endl;
                out << "(" << strings[i] << ")->" << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                out << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                num += 3;
                prove[i] = num - 1;
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> left -> left != NULL && trees[i] -> left -> right != NULL
                    && trees[i] -> left -> right -> value == trees[i] -> right -> value && trees[i] -> left -> operation == '&')
            {
                out << strings[i] << endl;
                out << "(" << strings[i] << ")->" << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                out << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                num += 3;
                prove[i] = num - 1;
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> right -> left != NULL && trees[i] -> right -> right != NULL
                    && trees[i] -> left -> value == trees[i] -> right -> left -> value && trees[i] -> right -> operation == '|')
            {
                out << strings[i] << endl;
                out << "(" << strings[i] << ")->" << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                out << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                num += 3;
                prove[i] = num - 1;
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> right -> left != NULL && trees[i] -> right -> right != NULL
                    && trees[i] -> left -> value == trees[i] -> right -> right -> value && trees[i] -> right -> operation == '|')
            {
                out << strings[i] << endl;
                out << "(" << strings[i] << ")->" << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                out << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                num += 3;
                prove[i] = num - 1;
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> left -> left != NULL && trees[i] -> left -> right != NULL && trees[i] -> right != NULL
                    && trees[i] -> right -> left != NULL && trees[i] -> right -> left -> left != NULL && trees[i] -> right -> left -> right != NULL
                    && trees[i] -> right -> right != NULL && trees[i] -> right -> right -> left != NULL && trees[i] -> right -> right -> left -> left != NULL
                    && trees[i] -> right -> right -> left -> right != NULL && trees[i] -> right -> right -> right != NULL
                    && trees[i] -> left -> left -> value == trees[i] -> right -> right -> left -> left -> value
                    && trees[i] -> right -> left -> left -> value == trees[i] -> right -> right -> left -> right -> value
                    && trees[i] -> left -> right -> value == trees[i] -> right -> left -> right -> value
                    && trees[i] -> left -> right -> value == trees[i] -> right -> right -> right -> value && trees[i] -> left -> operation == '-'
                    && trees[i] -> right -> operation == '-' && trees[i] -> right -> left -> operation == '-' && trees[i] -> right -> right -> operation == '-'
                    && trees[i] -> right -> right -> left -> operation == '|')
            {
                out << strings[i] << endl;
                out << "(" << strings[i] << ")->" << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                out << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                num += 3;
                prove[i] = num - 1;
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> left -> left != NULL && trees[i] -> left -> right != NULL && trees[i] -> right != NULL
                    && trees[i] -> right -> right != NULL && trees[i] -> right -> right -> left != NULL && trees[i] -> right -> left != NULL
                    && trees[i] -> right -> left -> left != NULL && trees[i] -> right -> left -> right != NULL && trees[i] -> right -> left -> right -> left != NULL
                    && trees[i] -> left -> left -> value == trees[i] -> right -> left -> left -> value
                    && trees[i] -> left -> left -> value == trees[i] -> right -> right -> left -> value
                    && trees[i] -> left -> right -> value == trees[i] -> right -> left -> right -> left -> value
                    && trees[i] -> left -> operation == '-' && trees[i] -> right -> operation == '-' && trees[i] -> right -> left -> operation == '-'
                    && trees[i] -> right -> left -> right -> operation == '!' && trees[i] -> right -> right -> operation == '!')
            {
                out << strings[i] << endl;
                out << "(" << strings[i] << ")->" << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                out << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                num += 3;
                prove[i] = num - 1;
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> left -> left != NULL && trees[i] -> left -> left -> left != NULL
                    && trees[i] -> right != NULL && trees[i] -> left -> left -> left -> value == trees[i] -> right -> value
                    && trees[i] -> left -> operation == '!' && trees[i] -> left -> left -> operation == '!')
            {
                out << strings[i] << endl;
                out << "(" << strings[i] << ")->" << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                out << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                num += 3;
                prove[i] = num - 1;
                flag = false;
            }
        }
        if (flag)
        {
            int p, q;
            string f;
            for (int j = n; j < i; j++)
            {
                if (trees[j] -> left != NULL && trees[j] -> right != NULL && trees[j] -> right -> value == trees[i] -> value && trees[j] -> operation == '-')
                {
                    need_for_MP.insert(trees[j] -> left -> value);
                }
            }
            for (int k = n; k < i; k++)
            {
                if (need_for_MP.find(trees[k] -> value) != need_for_MP.end())
                {
                    p = k;
                    f = trees[k] -> value;
                }
            }
            for (int j = n; j < i; j++)
            {
                if (trees[j] -> left != NULL && trees[j] -> right != NULL && trees[j] -> left -> value == f && trees[j] -> right -> value == trees[i] -> value)
                {
                    q = j;
                    flag = false;
                }
            }
            if (!flag)
            {
                string str = "";
                for (int j = 0; j < trees[q] -> right -> value.size(); j++)
                {
                    if (trees[q] -> right -> value[j] != '-')
                    {
                        str += trees[q] -> right -> value[j];
                    }
                    else
                    {
                        str += "->";
                    }
                }
                out << "(" << "(" << last << ")" << "->(" << strings[p] << "))" << "->" << "((" << "(" << last << ")" << "->(" << strings[q] << "))->(" << "(" << last << ")" << "->" << str << "))" << endl;
                out << "((" << "(" << last << ")" << "->(" << strings[q] << "))->(" << "(" << last << ")" << "->" << str << "))" << endl;
                out << "(" << last << ")" << "->" << str << endl;
                num += 3;
                prove[i] = num - 1;
            }
            while (!need_for_MP.empty())
            {
                need_for_MP.erase(need_for_MP.begin());
            }
        }
        if (trees[i] -> value == tree_last -> value)
        {
            out << "(" << last << ")" << "->" << "(" << last << ")" << "->" << "(" << last << ")" << endl;
            out << "(" << "(" << last << ")" << "->(" << "(" << last << ")" << "->" << "(" << last << ")" << "))->(" << "(" << last << ")" << "->((" << "(" << last << ")" << "->" << "(" << last << ")" << ")->" << "(" << last << ")" << "))->(" << "(" << last << ")" << "->" << "(" << last << ")" << ")" << endl;
            out << "(" << "(" << last << ")" << "->((" << "(" << last << ")" << "->" << "(" << last << ")" << ")->" << "(" << last << ")" << "))->(" << "(" << last << ")" << "->" << "(" << last << ")" << ")" << endl;
            out << "(" << "(" << last << ")" << "->((" << "(" << last << ")" << "->" << "(" << last << ")" << ")->" << "(" << last << ")" << "))" << endl;
            out << "(" << last << ")" << "->" << "(" << last << ")" << endl;
            num += 5;
            prove[i] = num - 1;
            flag = false;
        }
        if (flag)
        {
            for (int j = 0; j < n; j++)
            {
                if (strings[j] == strings[i])
                {
                    out << strings[i] << endl;
                    out << "(" << strings[i] << ")->" << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                    out << "(" << last << ")" << "->(" << strings[i] << ")" << endl;
                    num += 3;
                    prove[i] = num - 1;
                }
            }
            flag = false;
        }
    }
    return 0;
}