#include <iostream>
#include <cmath>
#include <algorithm>
#include <string>
#include <cstdio>
#include <vector>
#include <queue>
#include <set>
#include <stdexcept>
#include <map>
#include <fstream>

using namespace std;

vector <string> strings;
set <string> need_for_MP;
vector <string> new_prove;
set <string> my_variables;
vector <string> vector_my_variables;
bool need_watch_variables = true;
vector <string> binary_sequences;
string input_string;
map <string, vector <string> > proofs_for_binary_sequences;

struct node
{
    char operation;
    string value;
    bool binary_value;
    node *left;
    node *right;
    node *parent;
};

vector <node*> trees;
node* tree_last;
node* input_tree;

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
            if (need_watch_variables)
            {
                my_variables.insert(s);
            }
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

vector <string> deduction(vector <string> s, vector <string> assumptions)
{
    strings.clear();
    need_for_MP.clear();
    new_prove.clear();
    trees.clear();
    int n = (int) assumptions.size() - 1;
    string last = assumptions.back();
    for (int i = 0; i < assumptions.size() - 1; i++)
    {
        strings.push_back(assumptions[i]);
    }
    for (int i = 0; i < s.size(); i++)
    {
        strings.push_back(s[i]);
    }
    int all = (int) strings.size();
    tree_last = to_tree(to_stack(to_normal_string(last)));
    trees.resize(all);
    for (int i = n; i < all; i++)
    {
        bool flag = true;
        strings[i] = delete_spaces(strings[i]);
        trees[i] = to_tree(to_stack(to_normal_string(strings[i])));
        if (trees[i] -> operation == '-')
        {
            if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> right -> right != NULL
                    && trees[i] -> left -> value == trees[i] -> right -> right -> value && trees[i] -> right -> operation == '-')
            {
                new_prove.push_back(strings[i]);
                new_prove.push_back("(" + strings[i] + ")->" + "(" + last + ")" + "->(" + strings[i] + ")");
                new_prove.push_back("(" + last + ")" + "->(" + strings[i] + ")");
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
                new_prove.push_back(strings[i]);
                new_prove.push_back("(" + strings[i] + ")->" + "(" + last + ")" + "->(" + strings[i] + ")");
                new_prove.push_back("(" + last + ")" + "->(" + strings[i] + ")");
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> right -> left != NULL && trees[i] -> right -> right != NULL
                    && trees[i] -> right -> right -> left != NULL && trees[i] -> right -> right -> right != NULL
                    && trees[i] -> left -> value == trees[i] -> right -> right -> left -> value && trees[i] -> right -> left -> value == trees[i] -> right -> right -> right -> value
                    && trees[i] -> right -> operation == '-' && trees[i] -> right -> right -> operation == '&')
            {
                new_prove.push_back(strings[i]);
                new_prove.push_back("(" + strings[i] + ")->" + "(" + last + ")" + "->(" + strings[i] + ")");
                new_prove.push_back("(" + last + ")" + "->(" + strings[i] + ")");
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> left -> left != NULL && trees[i] -> left -> right != NULL
                    && trees[i] -> left -> left -> value == trees[i] -> right -> value && trees[i] -> left -> operation == '&')
            {
                new_prove.push_back(strings[i]);
                new_prove.push_back("(" + strings[i] + ")->" + "(" + last + ")" + "->(" + strings[i] + ")");
                new_prove.push_back("(" + last + ")" + "->(" + strings[i] + ")");
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> left -> left != NULL && trees[i] -> left -> right != NULL
                    && trees[i] -> left -> right -> value == trees[i] -> right -> value && trees[i] -> left -> operation == '&')
            {
                new_prove.push_back(strings[i]);
                new_prove.push_back("(" + strings[i] + ")->" + "(" + last + ")" + "->(" + strings[i] + ")");
                new_prove.push_back("(" + last + ")" + "->(" + strings[i] + ")");
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> right -> left != NULL && trees[i] -> right -> right != NULL
                    && trees[i] -> left -> value == trees[i] -> right -> left -> value && trees[i] -> right -> operation == '|')
            {
                new_prove.push_back(strings[i]);
                new_prove.push_back("(" + strings[i] + ")->" + "(" + last + ")" + "->(" + strings[i] + ")");
                new_prove.push_back("(" + last + ")" + "->(" + strings[i] + ")");
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> right != NULL && trees[i] -> right -> left != NULL && trees[i] -> right -> right != NULL
                    && trees[i] -> left -> value == trees[i] -> right -> right -> value && trees[i] -> right -> operation == '|')
            {
                new_prove.push_back(strings[i]);
                new_prove.push_back("(" + strings[i] + ")->" + "(" + last + ")" + "->(" + strings[i] + ")");
                new_prove.push_back("(" + last + ")" + "->(" + strings[i] + ")");
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
                new_prove.push_back(strings[i]);
                new_prove.push_back("(" + strings[i] + ")->" + "(" + last + ")" + "->(" + strings[i] + ")");
                new_prove.push_back("(" + last + ")" + "->(" + strings[i] + ")");
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
                new_prove.push_back(strings[i]);
                new_prove.push_back("(" + strings[i] + ")->" + "(" + last + ")" + "->(" + strings[i] + ")");
                new_prove.push_back("(" + last + ")" + "->(" + strings[i] + ")");
                flag = false;
            }
            else if (trees[i] -> left != NULL && trees[i] -> left -> left != NULL && trees[i] -> left -> left -> left != NULL
                    && trees[i] -> right != NULL && trees[i] -> left -> left -> left -> value == trees[i] -> right -> value
                    && trees[i] -> left -> operation == '!' && trees[i] -> left -> left -> operation == '!')
            {
                new_prove.push_back(strings[i]);
                new_prove.push_back("(" + strings[i] + ")->" + "(" + last + ")" + "->(" + strings[i] + ")");
                new_prove.push_back("(" + last + ")" + "->(" + strings[i] + ")");
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
                new_prove.push_back("((" + last + ")" + "->(" + strings[p] + "))" + "->" + "((" + "(" + last + ")" + "->(" + strings[q] + "))->(" + "(" + last + ")" + "->" + str + "))");
                new_prove.push_back("(((" + last + ")" + "->(" + strings[q] + "))->(" + "(" + last + ")" + "->" + str + "))");
                new_prove.push_back("(" + last + ")" + "->" + str);
            }
            while (!need_for_MP.empty())
            {
                need_for_MP.erase(need_for_MP.begin());
            }
        }
        if (trees[i] -> value == tree_last -> value)
        {
            new_prove.push_back("(" + last + ")" + "->" + "(" + last + ")" + "->" + "(" + last + ")");
            new_prove.push_back("((" + last + ")" + "->(" + "(" + last + ")" + "->" + "(" + last + ")" + "))->(" + "(" + last + ")" + "->((" + "(" + last + ")" + "->" + "(" + last + ")" + ")->" + "(" + last + ")" + "))->(" + "(" + last + ")" + "->" + "(" + last + ")" + ")");
            new_prove.push_back("((" + last + ")" + "->((" + "(" + last + ")" + "->" + "(" + last + ")" + ")->" + "(" + last + ")" + "))->(" + "(" + last + ")" + "->" + "(" + last + ")" + ")");
            new_prove.push_back("((" + last + ")" + "->((" + "(" + last + ")" + "->" + "(" + last + ")" + ")->" + "(" + last + ")" + "))");
            new_prove.push_back("(" + last + ")" + "->" + "(" + last + ")");
            flag = false;
        }
        if (flag)
        {
            for (int j = 0; j < n; j++)
            {
                if (strings[j] == strings[i])
                {
                    new_prove.push_back(strings[i]);
                    new_prove.push_back("(" + strings[i] + ")->" + "(" + last + ")" + "->(" + strings[i] + ")");
                    new_prove.push_back("(" + last + ")" + "->(" + strings[i] + ")");
                }
            }
            flag = false;
        }
    }
    return new_prove;
}

vector <string> contraposition (string a, string b)
{
    vector <string> s;
    s.push_back("(" + a + "->" + b + ")->(" + a + "->!" + b + ")->!" + a);
    s.push_back(a + "->" + b);
    s.push_back("(" + a + "->!" + b + ")->!" + a);
    s.push_back("!" + b + "->(" + a + "->!" + b + ")");
    s.push_back("!" + b);
    s.push_back(a + "->!" + b);
    s.push_back("!" + a);
    vector <string> assumptions;
    assumptions.push_back(a + "->" + b);
    assumptions.push_back("!" + b);
    s = deduction(s, assumptions);
    assumptions.pop_back();
    s = deduction(s, assumptions);
    return s;
}

vector <string> excthird(string a)
{
    a = "(" + a + ")";
    vector <string> res;
    res.push_back(a + "->" + a + "|!" + a);
    vector <string> contrapos = contraposition(a, "(" + a + "|!" + a + ")");
    for (int i = 0; i < contrapos.size(); i++)
    {
        res.push_back(contrapos[i]);
    }
    res.push_back("!(" + a + "|!" + a + ")->!" + a);
    res.push_back("!" + a + "->" + a + "|!" + a);
    contrapos = contraposition("!" + a, "(" + a + "|!" + a + ")");
    for (int i = 0; i < contrapos.size(); i++)
    {
        res.push_back(contrapos[i]);
    }
    res.push_back("!(" + a + "|!" + a + ")->!!" + a);
    res.push_back("(!(" + a + "|!" + a + ")->!" + a + ")->(!(" + a + "|!" + a + ")->!!" + a + ")->(!!(" + a + "|!" + a + "))");
    res.push_back("(!(" + a + "|!" + a + ")->!!" + a + ")->!!(" + a + "|!" + a + ")");
    res.push_back("!!(" + a + "|!" + a + ")");
    res.push_back("!!(" + a + "|!" + a + ")->(" + a + "|!" + a + ")");
    res.push_back(a + "|!" + a);
    return res;
}

vector <string> lemma_1(string x, string y)  // x, y |- x -> y
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = y + "->(" + x + "->" + y + ")";
    ans.push_back(str);
    str = y;
    ans.push_back(str);
    str = x + "->" + y;
    ans.push_back(str);
    return ans;
}

vector <string> lemma_2(string x, string y) // x, !y |- !(x -> y)
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = x;
    ans.push_back(str);
    str = "!" + y;
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + x + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "(" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = x + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + x;
    ans.push_back(str);
    str = "(" + x + "-" + ">" + y + ")" + "-" + ">" + x;
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "(" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = "!" + y + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "!" + y;
    ans.push_back(str);
    str = "(" + x + "-" + ">" + y + ")" + "-" + ">" + "!" + y;
    ans.push_back(str);
    str = "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + x + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + x + ")" + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + x + ")" + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "(!" + y + "-" + ">" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = "(!" + y + "-" + ">" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "!" + y + "-" + ">" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "!" + y + "-" + ">" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "!" + y + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "!" + y + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")" + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "!" + y + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")" + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")" + ")" + "-" + ">" + "(" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + x + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "!" + x;
    ans.push_back(str);
    str = "((" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + x + ")" + "-" + ">" + "(" + x + "-" + ">" + y + ")" + "-" + ">" + "!" + x;
    ans.push_back(str);
    str = "(" + x + "-" + ">" + y + ")" + "-" + ">" + "!" + x;
    ans.push_back(str);
    str = "!(" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    return ans;
}

vector <string> lemma_3(string x, string y) // !x, y |- x -> y
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = y + "->(" + x + "->" + y + ")";
    ans.push_back(str);
    str = y;
    ans.push_back(str);
    str = x + "->" + y;
    ans.push_back(str);
    return ans;
}

vector <string> lemma_4(string x, string y) // !x, !y |- x -> y
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = "!" + x;
    ans.push_back(str);
    str = "!" + x + "-" + ">" + x + "-" + ">" + "!" + x;
    ans.push_back(str);
    str = x + "-" + ">" + "!" + x;
    ans.push_back(str);
    str = "!" + y;
    ans.push_back(str);
    str = "!" + y + "-" + ">" + x + "-" + ">" + "!" + y;
    ans.push_back(str);
    str = x + "-" + ">" + "!" + y;
    ans.push_back(str);
    str = x + "-" + ">" + x + "-" + ">" + x;
    ans.push_back(str);
    str = "(" + x + "-" + ">" + x + "-" + ">" + x + ")" + "-" + ">" + "(" + x + "-" + ">" + "(" + x + "-" + ">" + x + ")" + "-" + ">" + x + ")" + "-" + ">" + x + "-" + ">" + x;
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "(" + x + "-" + ">" + x + ")" + "-" + ">" + x + ")" + "-" + ">" + x + "-" + ">" + x;
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "(" + x + "-" + ">" + x + ")" + "-" + ">" + x + ")";
    ans.push_back(str);
    str = x + "-" + ">" + x;
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "!" + y + "-" + ">" + x + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "!" + y + "-" + ">" + x + ")" + "-" + ">" + x + "-" + ">" + "(" + x + "-" + ">" + "!" + y + "-" + ">" + x + ")";
    ans.push_back(str);
    str = x + "-" + ">" + "(" + x + "-" + ">" + "!" + y + "-" + ">" + x + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + x + ")" + "-" + ">" + "(" + x + "-" + ">" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + x + ")" + ")" + "-" + ">" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + x + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + x + ")" + ")" + "-" + ">" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + x + ")";
    ans.push_back(str);
    str = x + "-" + ">" + "(" + "!" + y + "-" + ">" + x + ")";
    ans.push_back(str);
    str = "(!" + x + "-" + ">" + "!" + y + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "(!" + x + "-" + ">" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + x + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = x + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "!" + x + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + ")" + "-" + ">" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "!" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + ")" + "-" + ">" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = x + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "((!" + y + "-" + ">" + x + ")" + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + y + ")";
    ans.push_back(str);
    str = "((!" + y + "-" + ">" + x + ")" + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + y + ")" + "-" + ">" + x + "-" + ">" + "(" + "(" + "!" + y + "-" + ">" + x + ")" + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + y + ")";
    ans.push_back(str);
    str = x + "-" + ">" + "(" + "(" + "!" + y + "-" + ">" + x + ")" + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + y + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + x + ")" + ")" + "-" + ">" + "(" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + x + ")" + "-" + ">" + "(" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + y + ")" + ")" + "-" + ">" + x + "-" + ">" + "(" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + y + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + x + ")" + "-" + ">" + "(" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + y + ")" + ")" + "-" + ">" + x + "-" + ">" + "(" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + y + ")";
    ans.push_back(str);
    str = x + "-" + ">" + "(" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + y + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + ")" + "-" + ">" + "(" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + y + ")" + "-" + ">" + x + "-" + ">" + "!" + "!" + y;
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + y + ")" + "-" + ">" + x + "-" + ">" + "!" + "!" + y;
    ans.push_back(str);
    str = x + "-" + ">" + "!" + "!" + y;
    ans.push_back(str);
    str = "(!!" + y + "-" + ">" + y + ")";
    ans.push_back(str);
    str = "(!!" + y + "-" + ">" + y + ")" + "-" + ">" + x + "-" + ">" + "(" + "!" + "!" + y + "-" + ">" + y + ")";
    ans.push_back(str);
    str = x + "-" + ">" + "(" + "!" + "!" + y + "-" + ">" + y + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "!" + "!" + y + ")" + "-" + ">" + "(" + x + "-" + ">" + "!" + "!" + y + "-" + ">" + y + ")" + "-" + ">" + x + "-" + ">" + y;
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "!" + "!" + y + "-" + ">" + y + ")" + "-" + ">" + x + "-" + ">" + y;
    ans.push_back(str);
    str = x + "-" + ">" + y;
    ans.push_back(str);
    return ans;
}

vector <string> lemma_5(string x, string y) // x, y |- x & y
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = x + "->(" + y + "->(" + x + "&" + y + "))";
    ans.push_back(str);
    str = x;
    ans.push_back(str);
    str = y + "->(" + x + "&" + y + ")";
    ans.push_back(str);
    str = y;
    ans.push_back(str);
    str = x + "&" + y;
    ans.push_back(str);
    return ans;
}

vector <string> lemma_6(string x, string y) // x, !y |- !(x & y)
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = "!" + y + "->((" + x + "&" + y + ")->!" + y + ")";
    ans.push_back(str);
    str = "!" + y;
    ans.push_back(str);
    str = "(" + x + "&" + y + ")->!" + y;
    ans.push_back(str);
    str = "(" + x + "&" + y + ")->" + y;
    ans.push_back(str);
    str = "((" + x + "&" + y + ")->" + y + ")->(((" + x + "&" + y + ")->!" + y + ")->!(" + x + "&" + y + "))";
    ans.push_back(str);
    str = "((" + x + "&" + y + ")->!" + y + ")->!(" + x + "&" + y + ")";
    ans.push_back(str);
    str = "!(" + x + "&" + y + ")";
    ans.push_back(str);
    return ans;
}

vector <string> lemma_7(string x, string y) // !x, y |- !(x & y)
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = "!" + x + "->((" + x + "&" + y + ")->!" + x + ")";
    ans.push_back(str);
    str = "!" + x;
    ans.push_back(str);
    str = "(" + x + "&" + y + ")->!" + x;
    ans.push_back(str);
    str = "(" + x + "&" + y + ")->" + x;
    ans.push_back(str);
    str = "((" + x + "&" + y + ")->" + x + ")->(((" + x + "&" + y + ")->!" + x + ")->!(" + x + "&" + y + "))";
    ans.push_back(str);
    str = "((" + x + "&" + y + ")->!" + x + ")->!(" + x + "&" + y + ")";
    ans.push_back(str);
    str = "!(" + x + "&" + y + ")";
    ans.push_back(str);
    return ans;
}

vector <string> lemma_8(string x, string y) // !x, !y |- !(x & y)
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = "!" + y + "->((" + x + "&" + y + ")->!" + y + ")";
    ans.push_back(str);
    str = "!" + y;
    ans.push_back(str);
    str = "(" + x + "&" + y + ")->!" + y;
    ans.push_back(str);
    str = "(" + x + "&" + y + ")->" + y;
    ans.push_back(str);
    str = "((" + x + "&" + y + ")->" + y + ")->(((" + x + "&" + y + ")->!" + y + ")->!(" + x + "&" + y + "))";
    ans.push_back(str);
    str = "((" + x + "&" + y + ")->!" + y + ")->!(" + x + "&" + y + ")";
    ans.push_back(str);
    str = "!(" + x + "&" + y + ")";
    ans.push_back(str);
    return ans;
}

vector <string> lemma_9(string x, string y) // x, y |- x | y
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = x + "->(" + x + "|" + y + ")";
    ans.push_back(str);
    str = x;
    ans.push_back(str);
    str = x + "|" + y;
    ans.push_back(str);
    return ans;
}

vector <string> lemma_10(string x, string y) // x, !y |- x | y
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = x + "->(" + x + "|" + y + ")";
    ans.push_back(str);
    str = x;
    ans.push_back(str);
    str = x + "|" + y;
    ans.push_back(str);
    return ans;
}

vector <string> lemma_11(string x, string y) // !x, y |- x | y
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = y + "->(" + x + "|" + y + ")";
    ans.push_back(str);
    str = y;
    ans.push_back(str);
    str = x + "|" + y;
    ans.push_back(str);
    return ans;
}

vector <string> lemma_12(string x, string y) // !x, !y |- !(x | y)
{
    x = "(" + x + ")";
    y = "(" + y + ")";
    vector <string> ans;
    string str;
    str = "!" + x;
    ans.push_back(str);
    str = "!" + y;
    ans.push_back(str);
    str = "(" + x + "|" + y + "-" + ">" + x + ")" + "-" + ">" + "(" + x + "|" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "(" + x + "|" + y + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + x + ")" + "-" + ">" + "(" + y + "-" + ">" + x + ")" + "-" + ">" + "(" + x + "|" + y + "-" + ">" + x + ")";
    ans.push_back(str);
    str = x + "-" + ">" + x + "-" + ">" + x;
    ans.push_back(str);
    str = "(" + x + "-" + ">" + x + "-" + ">" + x + ")" + "-" + ">" + "(" + x + "-" + ">" + "(" + x + "-" + ">" + x + ")" + "-" + ">" + x + ")" + "-" + ">" + "(" + x + "-" + ">" + x + ")";
    ans.push_back(str);
    str = "(" + x + "-" + ">" + "(" + x + "-" + ">" + x + ")" + "-" + ">" + x + ")" + "-" + ">" + "(" + x + "-" + ">" + x + ")";
    ans.push_back(str);
    str = x + "-" + ">" + "(" + x + "-" + ">" + x + ")" + "-" + ">" + x;
    ans.push_back(str);
    str = x + "-" + ">" + x;
    ans.push_back(str);
    str = "(" + y + "-" + ">" + x + ")" + "-" + ">" + "(" + x + "|" + y + "-" + ">" + x + ")";
    ans.push_back(str);
    str = "!" + y + "-" + ">" + y + "-" + ">" + "!" + y;
    ans.push_back(str);
    str = y + "-" + ">" + "!" + y;
    ans.push_back(str);
    str = y + "-" + ">" + y + "-" + ">" + y;
    ans.push_back(str);
    str = "(" + y + "-" + ">" + y + "-" + ">" + y + ")" + "-" + ">" + "(" + y + "-" + ">" + "(" + y + "-" + ">" + y + ")" + "-" + ">" + y + ")" + "-" + ">" + y + "-" + ">" + y;
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "(" + y + "-" + ">" + y + ")" + "-" + ">" + y + ")" + "-" + ">" + y + "-" + ">" + y;
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "(" + y + "-" + ">" + y + ")" + "-" + ">" + y + ")";
    ans.push_back(str);
    str = y + "-" + ">" + y;
    ans.push_back(str);
    str = "(!!" + x + "-" + ">" + x + ")";
    ans.push_back(str);
    str = "(!!" + x + "-" + ">" + x + ")" + "-" + ">" + y + "-" + ">" + "(" + "!" + "!" + x + "-" + ">" + x + ")";
    ans.push_back(str);
    str = y + "-" + ">" + "(" + "!" + "!" + x + "-" + ">" + x + ")";
    ans.push_back(str);
    str = "((!" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + "!" + x + ")";
    ans.push_back(str);
    str = "((!" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + "!" + x + ")" + "-" + ">" + y + "-" + ">" + "(" + "(" + "!" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + "!" + x + ")";
    ans.push_back(str);
    str = y + "-" + ">" + "(" + "(" + "!" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + "!" + x + ")";
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "!" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "!" + x + "-" + ">" + y + ")" + "-" + ">" + y + "-" + ">" + "(" + y + "-" + ">" + "!" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = y + "-" + ">" + "(" + y + "-" + ">" + "!" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = "(" + y + "-" + ">" + y + ")" + "-" + ">" + "(" + y + "-" + ">" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + y + ")" + ")" + "-" + ">" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = "(" + y + "-" + ">" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + y + ")" + ")" + "-" + ">" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = y + "-" + ">" + "(" + "!" + x + "-" + ">" + y + ")";
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + y + ")" + ")" + "-" + ">" + "(" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + "!" + x + ")" + ")" + "-" + ">" + y + "-" + ">" + "(" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + "!" + x + ")";
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + y + ")" + "-" + ">" + "(" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + "!" + x + ")" + ")" + "-" + ">" + y + "-" + ">" + "(" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + "!" + x + ")";
    ans.push_back(str);
    str = y + "-" + ">" + "(" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + "!" + x + ")";
    ans.push_back(str);
    str = "(!" + y + "-" + ">" + "!" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = "(!" + y + "-" + ">" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + y + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = y + "-" + ">" + "(" + "!" + y + "-" + ">" + "!" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "!" + y + ")" + "-" + ">" + "(" + y + "-" + ">" + "!" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + ")" + "-" + ">" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "!" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + ")" + "-" + ">" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = y + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")";
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + ")" + "-" + ">" + "(" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + "!" + x + ")" + "-" + ">" + y + "-" + ">" + "!" + "!" + x;
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + y + ")" + "-" + ">" + "!" + "!" + x + ")" + "-" + ">" + y + "-" + ">" + "!" + "!" + x;
    ans.push_back(str);
    str = y + "-" + ">" + "!" + "!" + x;
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "!" + "!" + x + ")" + "-" + ">" + "(" + y + "-" + ">" + "!" + "!" + x + "-" + ">" + x + ")" + "-" + ">" + y + "-" + ">" + x;
    ans.push_back(str);
    str = "(" + y + "-" + ">" + "!" + "!" + x + "-" + ">" + x + ")" + "-" + ">" + y + "-" + ">" + x;
    ans.push_back(str);
    str = y + "-" + ">" + x;
    ans.push_back(str);
    str = x + "|" + y + "-" + ">" + x;
    ans.push_back(str);
    str = "(" + x + "|" + y + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "(" + x + "|" + y + ")";
    ans.push_back(str);
    str = "!" + x + "-" + ">" + x + "|" + y + "-" + ">" + "!" + x;
    ans.push_back(str);
    str = x + "|" + y + "-" + ">" + "!" + x;
    ans.push_back(str);
    str = "!(" + x + "|" + y + ")";
    ans.push_back(str);
    return ans;
}

vector <string> lemma_13(string x) // x |- !!x
{
    x = "(" + x + ")";
    vector<string> ans;
    string str;
    str = x;
    ans.push_back(str);
    str = "(!" + x + "-" + ">" + x + ")" + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + x;
    ans.push_back(str);
    str = x + "-" + ">" + "!" + x + "-" + ">" + x;
    ans.push_back(str);
    str = "!" + x + "-" + ">" + x;
    ans.push_back(str);
    str = "(!" + x + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + "!" + x;
    ans.push_back(str);
    str = "!" + x + "-" + ">" + "!" + x + "-" + ">" + "!" + x;
    ans.push_back(str);
    str = "(!" + x + "-" + ">" + "!" + x + "-" + ">" + "!" + x + ")" + "-" + ">" + "(" + "!" + x + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + x + ")" + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "(!" + x + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + x + ")" + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + x + ")";
    ans.push_back(str);
    str = "!" + x + "-" + ">" + "(" + "!" + x + "-" + ">" + "!" + x + ")" + "-" + ">" + "!" + x;
    ans.push_back(str);
    str = "!" + x + "-" + ">" + "!" + x;
    ans.push_back(str);
    str = "!!" + x;
    ans.push_back(str);
    return ans;
}

vector <string> lemma_14(string x) // !x -> !x
{
    x = "(" + x + ")";
    vector <string> ans;
    string str;
    str = "!" + x;
    ans.push_back(str);
    return ans;
}

bool check_true(node* tree, string sequence)
{
    if (tree -> left == NULL && tree -> right == NULL)
    {
        for (int i = 0; i < vector_my_variables.size(); i++)
        {
            if (tree -> value == vector_my_variables[i])
            {
                if (sequence[i] == '0')
                {
                    tree -> binary_value = false;
                    return false;
                }
                else
                {
                    tree -> binary_value = true;
                    return true;
                }
            }
        }
    }
    if (tree -> operation == '|')
    {
        bool left = check_true(tree -> left, sequence);
        bool right = check_true(tree -> right, sequence);
        tree -> binary_value = (left || right);
        return tree -> binary_value;
    }
    else if (tree -> operation == '&')
    {
        bool left = check_true(tree -> left, sequence);
        bool right = check_true(tree -> right, sequence);
        tree -> binary_value = (left && right);
        return tree -> binary_value;
    }
    else if (tree -> operation == '-')
    {
        bool left = check_true(tree -> left, sequence);
        bool right = check_true(tree -> right, sequence);
        if (left && !right)
        {
            tree -> binary_value = false;
            return false;
        }
        else
        {
            tree -> binary_value = true;
            return true;
        }
    }
    else if (tree -> operation == '!')
    {
        bool left = check_true(tree -> left, sequence);
        tree -> binary_value = (!left);
        return tree -> binary_value;
    }
}

void gen(string s)
{
    if (s.size() == vector_my_variables.size())
    {
        binary_sequences.push_back(s);
        return;
    }
    gen(s + "0");
    gen(s + "1");
}

vector <string> proof(node* tree)
{
    vector <string> proofs;
    if (tree -> left == NULL && tree -> right == NULL)
    {
        if (tree -> binary_value)
        {
            proofs.push_back(tree -> value);
        }
        else
        {
            proofs.push_back("!" + tree -> value);
        }
    }
    else if (tree -> operation == '-')
    {
        if (tree -> left -> binary_value == false && tree -> right -> binary_value == false)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_4(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
        else if (tree -> left -> binary_value == false && tree -> right -> binary_value == true)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_3(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
        else if (tree -> left -> binary_value == true && tree -> right -> binary_value == false)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_2(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
        else if (tree -> left -> binary_value == true && tree -> right -> binary_value == true)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_1(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
    }
    else if (tree -> operation == '&')
    {
        if (tree -> left -> binary_value == false && tree -> right -> binary_value == false)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_8(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
        else if (tree -> left -> binary_value == false && tree -> right -> binary_value == true)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_7(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
        else if (tree -> left -> binary_value == true && tree -> right -> binary_value == false)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_6(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
        else if (tree -> left -> binary_value == true && tree -> right -> binary_value == true)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_5(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
    }
    else if (tree -> operation == '|')
    {
        if (tree -> left -> binary_value == false && tree -> right -> binary_value == false)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_12(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
        else if (tree -> left -> binary_value == false && tree -> right -> binary_value == true)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_11(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
        else if (tree -> left -> binary_value == true && tree -> right -> binary_value == false)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_10(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
        else if (tree -> left -> binary_value == true && tree -> right -> binary_value == true)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> right = proof(tree -> right);
            for (int i = 0; i < right.size(); i++)
            {
                proofs.push_back(right[i]);
            }
            vector <string> curr = lemma_9(tree -> left -> value, tree -> right -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
    }
    else
    {
        if (tree -> left -> binary_value == false)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> curr = lemma_14(tree -> left -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
        else if (tree -> left -> binary_value == true)
        {
            vector <string> left = proof(tree -> left);
            for (int i = 0; i < left.size(); i++)
            {
                proofs.push_back(left[i]);
            }
            vector <string> curr = lemma_13(tree -> left -> value);
            for (int i = 0; i < curr.size(); i++)
            {
                proofs.push_back(curr[i]);
            }
        }
    }
    return proofs;
}

vector <string> exception_assumption(vector <string> first_proof, vector <string> second_proof, string final_result, string assumption)
{
    vector <string> final_proof;
    set <string> was_proved;
    for (int i = 0; i < first_proof.size(); i++)
    {
        if (was_proved.find(first_proof[i]) != was_proved.end())
        {
            continue;
        }
        final_proof.push_back(first_proof[i]);
        was_proved.insert(first_proof[i]);
    }
    for (int i = 0; i < second_proof.size(); i++)
    {
        if (was_proved.find(second_proof[i]) != was_proved.end())
        {
            continue;
        }
        final_proof.push_back(second_proof[i]);
        was_proved.insert(second_proof[i]);
    }
    vector <string> exthird = excthird(assumption);
    for (int i = 0; i < exthird.size(); i++)
    {
        if (was_proved.find(exthird[i]) != was_proved.end())
        {
            continue;
        }
        final_proof.push_back(exthird[i]);
        was_proved.insert(exthird[i]);
    }
    final_proof.push_back("(" + assumption + "->" + final_result + ")->(!" + assumption + "->" + final_result + ")->(" + assumption + "|!" + assumption + ")->" + final_result);
    final_proof.push_back("(!" + assumption + "->" + final_result + ")->(" + assumption + "|!" + assumption + "->" + final_result + ")");
    final_proof.push_back(assumption + "|!" + assumption + "->" + final_result);
    final_proof.push_back(final_result);
    return final_proof;
}

void get_full_proof(int number_of_assumptions, vector <string> sequences)
{
    for (int j = 0; j < sequences.size(); j++)
    {
        string first_string = "1" + sequences[j];
        vector <string> first_proof = proofs_for_binary_sequences[first_string];
        string second_string = "0" + sequences[j];
        vector <string> second_proof = proofs_for_binary_sequences[second_string];
        string last_in_second_proof = second_proof.back();
        int i = 0;
        int balance_brackets = 0; // на случай (assumption -> expression), то есть перед первым assumption стоит скобка, которая закрывается в конце выражения
        while (last_in_second_proof[i] != '-')
        {
            if (last_in_second_proof[i] == '(')
            {
                balance_brackets++;
            }
            else if (last_in_second_proof[i] == ')')
            {
                balance_brackets--;
            }
            i++;
        }
        string to_delete = last_in_second_proof.substr(0, i);
        int q = 0;
        while (!is_ident(to_delete[q]))
        {
            q++;
        }
        int k = q;
        while (is_ident(to_delete[k]))
        {
            k++;
        }
        to_delete = to_delete.substr(q, k - q);
        string interesting_string = last_in_second_proof.substr(i + 2, last_in_second_proof.size() - i - 1);
        interesting_string = interesting_string.substr(0, interesting_string.size() - balance_brackets);
        vector <string> current_proof = exception_assumption(first_proof, second_proof, interesting_string, to_delete);
        proofs_for_binary_sequences.insert(make_pair(sequences[j], current_proof));
    }
}

int main() {
    ifstream in("full.in");
    ofstream out("full.out");
    getline(in, input_string);
    input_tree = to_tree(to_stack(to_normal_string(input_string)));
    need_watch_variables = false;
    for (set <string>::iterator it = my_variables.begin(); it != my_variables.end(); it++)
    {
        vector_my_variables.push_back(*it);
    }
    gen("");
    for (int i = 0; i < binary_sequences.size(); i++)
    {
        if (!check_true(input_tree, binary_sequences[i]))
        {
            out << "Высказавание ложно при ";
            for (int j = 0; j < vector_my_variables.size(); j++)
            {
                out << vector_my_variables[j] << "=";
                if (binary_sequences[i][j] == '0')
                {
                    out << "Л";
                }
                else
                {
                    out << "И";
                }
                if (j != vector_my_variables.size() - 1)
                {
                    out << ", ";
                }
            }
            return 0;
        }
    }
    for (int i = 0; i < binary_sequences.size(); i++)
    {
        check_true(input_tree, binary_sequences[i]);
        vector<string> res = proof(input_tree);
        vector<string> assumpts;
        for (int j = 0; j < vector_my_variables.size(); j++)
        {
            if (binary_sequences[i][j] == '0')
            {
                assumpts.push_back("!" + vector_my_variables[j]);
            }
            else
            {
                assumpts.push_back(vector_my_variables[j]);
            }
        }
        int assumpts_size = (int) assumpts.size();
        for (int i = 0; i < assumpts_size; i++)
        {
            res = deduction(res, assumpts);
            assumpts.pop_back();
        }
        proofs_for_binary_sequences.insert(make_pair(binary_sequences[i], res));
    }
    int size = (int) vector_my_variables.size() - 1;
    int first_elements = 1 << size;
    vector <string> elements;
    while (size > -1)
    {
        for (int i = 0; i < first_elements; i++)
        {
            elements.push_back(binary_sequences[i].substr(vector_my_variables.size() - size, size));
        }
        get_full_proof(size, elements);
        size--;
        first_elements = 1 << size;
        elements.clear();
    }
    vector <string> result_proof = proofs_for_binary_sequences[""];
    for (int i = 0; i < result_proof.size(); i++)
    {
        out << result_proof[i] << endl;
    }
    return 0;
}