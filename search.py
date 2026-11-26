"""Generic tabled agenda: AND premises, OR rules, output-dependent questions.

Only completed answers wake waiting applications. A pending cycle cannot seed
an answer. All mathematical rules live in the separately loaded library.
"""
from collections import OrderedDict, deque
from heapq import heapify, heappop, heappush
from dataclasses import dataclass
from model import canonical, digest, freeze, match, instantiate, size, Unsupported
from polynomial import ResourceBound


@dataclass
class Limits:
    jobs: int | None = None
    questions: int | None = 2000
    term_nodes: int | None = 256
    depth: int | None = 32

    @classmethod
    def exhaustive(cls):
        """Enumerate admitted rule applications without agenda or depth caps."""
        return cls(questions=None,term_nodes=None,depth=None)


class FairDeferred:
    """Alternate the oldest application and the best-ranked one, with stable ties."""
    def __init__(self,questions,priority):
        self.questions,self.priority=questions,priority
        self.jobs,self.heap=OrderedDict(),[]
        self.serial,self.oldest=0,True

    def __len__(self):return len(self.jobs)

    def append(self,job):
        question=self.questions[job[1][0]]
        if 'priority' not in question:question['priority']=self.priority(question['goal'])
        rank=question['priority']
        self.jobs[self.serial]=(rank,job)
        heappush(self.heap,(rank,self.serial))
        self.serial+=1

    def popleft(self):
        if self.oldest:
            _,(_,job)=self.jobs.popitem(last=False)
        else:
            while self.heap[0][1] not in self.jobs:heappop(self.heap)
            _,key=heappop(self.heap)
            _,job=self.jobs.pop(key)
        self.oldest=not self.oldest
        if len(self.heap)>2*len(self.jobs)+64:
            self.heap=[(rank,key) for key,(rank,_) in self.jobs.items()]
            heapify(self.heap)
        return job


class Engine:
    def __init__(self, library, ctx, limits=None, operations=None, *, required_rules=None, task_kind='', witness_rule=None, deferred_priority=None, all_proofs=False, max_proof_steps=None, trace_rules=False):
        self.library, self.ctx = library,ctx
        self.context_hash = digest(ctx)
        self.limits = limits or Limits()
        self.compute = operations or library.compute
        self.required_rules = required_rules or {}
        self.task_kind = task_kind
        self.witness_rule = witness_rule
        self.witnessed = set()
        self.queue = deque()
        self.questions = {}
        self.deferred = FairDeferred(self.questions,deferred_priority) if deferred_priority else deque()
        self.deferred_turn = None
        self.proofs = {}
        self.all_proofs = all_proofs
        if max_proof_steps is not None and (not all_proofs or type(max_proof_steps) is not int or max_proof_steps < 0):
            raise ValueError('max_proof_steps requires all_proofs and a nonnegative integer')
        self.max_proof_steps = max_proof_steps
        self.enumeration_complete = False
        self.complete_through_steps = None
        self.excluded_by_size = False
        self.depth_limit = self.limits.depth
        # A proof DAG of size N can only ask questions at most N-1 edges away.
        self.depth_from_steps = max_proof_steps is not None and (self.depth_limit is None or max_proof_steps-1 <= self.depth_limit)
        if self.depth_from_steps:
            self.depth_limit = max_proof_steps-1
        if all_proofs:
            self.proof_nodes = {}
            self.derivations = set()
        self.rejections = []
        self.rule_attempts = {} if trace_rules else None
        self.cutoffs = set()
        self.depth_waiters = []
        self.processed = 0
        self.applications = 0
        self.skipped_truth = 0

    def ensure(self, goal, depth, waiter=None):
        goal = freeze(goal)
        key = canonical(goal)
        if key in self.questions:
            if depth < self.questions[key]['depth']:
                self.questions[key]['depth'] = depth
            return key
        if self.depth_limit is not None and depth > self.depth_limit:
            if not self.depth_from_steps:
                self.cutoffs.add("depth")
            if waiter is not None:
                self.depth_waiters.append((key,waiter))
            else:
                self.excluded_by_size = True  # A zero-step bound excludes the root.
            return None
        if self.limits.term_nodes is not None and size(goal) > self.limits.term_nodes:
            self.cutoffs.add("expression_size")
            return None
        if self.limits.questions is not None and len(self.questions) >= self.limits.questions:
            self.cutoffs.add("question_count")
            return None
        try:
            self.library.validate(goal,self.ctx)
        except Unsupported:
            self.cutoffs.add("generated_language_limit")
            return None
        self.questions[key] = {"goal":goal,"answers":[],"waiters":[],"depth":depth}
        self.queue.append(("expand",key))
        return key

    def answers(self, goal):
        record = self.questions.get(canonical(goal))
        return record["answers"] if record else []

    def retry_depth_waiters(self):
        """A shared question may have acquired a shorter route after its first expansion."""
        if not self.depth_waiters:return False
        children = {}
        for child,question in self.questions.items():
            for waiter in question['waiters']:
                children.setdefault(waiter[0],set()).add(child)
        roots = [key for key,q in self.questions.items() if q['depth']==0]
        todo,seen = deque(roots),set(roots)
        while todo:
            key = todo.popleft()
            for child in children.get(key,()):
                if child not in seen:
                    seen.add(child)
                    self.questions[child]['depth'] = self.questions[key]['depth']+1
                    todo.append(child)
        pending,self.depth_waiters = self.depth_waiters,[]
        for child,waiter in pending:
            if child in self.questions or self.questions[waiter[0]]['depth'] < self.depth_limit:
                self.queue.append(('advance',waiter))
            else:
                self.depth_waiters.append((child,waiter))
        if not self.depth_waiters:self.cutoffs.discard('depth')
        return bool(self.queue)

    def resume(self, job, answer):
        key,rid,env,i,trace = job
        r = self.library.by_id[rid]
        step = r["steps"][i]
        env = dict(env)
        if not match(step.get("bind",True),answer["value"],env):
            self.rejections.append({"rule":rid,"goal":self.questions[key]["goal"],"reason":"output_constraint", "value":answer["value"]})
            return
        entry = {"ask":instantiate(step["ask"],env),"proof":answer["proof"],"value":answer["value"]}
        self.queue.append(("advance",(key,rid,env,i+1,trace+[entry])))

    def publish(self, key, rid, env, trace):
        r = self.library.by_id[rid]
        value = freeze(instantiate(r["result"],env))
        question = self.questions[key]
        try:
            self.library.validate(question["goal"],self.ctx,value,True)
        except Unsupported:
            self.cutoffs.add("generated_language_limit")
            return
        witnessed = self.witness_rule and self.witness_rule(r,value,trace,self.witnessed)
        value_key = canonical(value)
        same_value_proofs=question.setdefault('proofs_by_value',{}).setdefault(value_key,[])
        if self.all_proofs:
            support = frozenset().union(*(self.proof_nodes[s['proof']] for s in trace if 'proof' in s))
            # Sibling premises may share a fact. Only a repeated (goal, value)
            # on the same branch would use the conclusion to establish itself.
            if not support.isdisjoint(same_value_proofs):
                return
            if self.max_proof_steps is not None and len(support)+1 > self.max_proof_steps:
                self.excluded_by_size = True
                return
            # Ordered premise proofs and primitive outputs identify the derivation.
            # Duplicate operation results do not create another mathematical proof.
            signature = (key, value_key, rid, canonical(trace))
            if signature in self.derivations:
                return
            self.derivations.add(signature)
        elif same_value_proofs and (not witnessed or any(pid in self.witnessed for pid in same_value_proofs)):
            return
        pid = f"p{len(self.proofs)+1}"
        node = {"id":pid,"goal":question["goal"],"value":value,"rule":rid,
                "revision":self.library.revisions[rid],"context":self.context_hash,"steps":trace}
        self.proofs[pid] = node
        if self.all_proofs:
            self.proof_nodes[pid] = support | {pid}
        same_value_proofs.append(pid)
        if witnessed:self.witnessed.add(pid)
        answer = {"value":value,"proof":pid}
        question["answers"].append(answer)
        for waiter in list(question["waiters"]):
            self.resume(waiter,answer)

    def run(self, roots, stop=None):
        self.enumeration_complete = False
        self.complete_through_steps = None
        for root in roots:
            self.ensure(root,0)
        while self.queue or self.deferred or self.retry_depth_waiters():
            if stop and stop(self):
                break
            if self.limits.jobs is not None and self.processed >= self.limits.jobs:
                self.cutoffs.add("jobs")
                break
            self.processed += 1
            if self.queue and self.deferred and self.deferred_turn is None:
                free = (1 if self.limits.questions is None else
                        max(1,self.limits.questions-len(self.questions)))
                # Share remaining slots geometrically. The job interval also covers
                # ordinary work that keeps running without admitting new questions.
                self.deferred_turn = self.processed+len(self.queue)*free, len(self.questions)+(free+1)//2
            take_deferred = self.deferred and (not self.queue or self.processed>=self.deferred_turn[0]
                                               or len(self.questions)>=self.deferred_turn[1])
            if take_deferred or not self.deferred:
                self.deferred_turn = None
            kind,data = (self.deferred if take_deferred else self.queue).popleft()
            if kind == "expand":
                rec = self.questions[data]
                required = self.required_rules.get(rec['goal'])
                for r,env in self.library.candidates(rec["goal"],self.ctx):
                    if required is not None and r['id'] != required:
                        continue
                    self.applications += 1
                    later = r.get('deferred',False) or r.get('defer_for_goal') == self.task_kind
                    queue = self.deferred if later else self.queue
                    queue.append(("advance",(data,r["id"],env,0,[])))
                continue
            key,rid,env,i,trace = data
            question=self.questions[key]
            if not self.all_proofs and question['answers'] and self.library.data['predicates'][question['goal'][0]]['output']=='truth':
                self.skipped_truth+=1
                continue
            r = self.library.by_id[rid]
            if i==0 and self.rule_attempts is not None:self.rule_attempts.setdefault(key,[]).append(rid)
            if i == len(r["steps"]):
                self.publish(key,rid,env,trace)
                continue
            step = r["steps"][i]
            if "ask" in step:
                goal = instantiate(step["ask"],env)
                child = self.ensure(goal,question['depth']+1,data)
                if child is None:
                    continue
                self.questions[child]["waiters"].append(data)
                for answer in list(self.questions[child]["answers"]):
                    self.resume(data,answer)
            else:
                args = instantiate(step.get("args",[]),env)
                try:
                    outputs = self.compute(step["op"],args,self.ctx)
                except ResourceBound:
                    self.cutoffs.add("primitive_arithmetic")
                    continue
                if not outputs:
                    self.rejections.append({"rule":rid,"goal":self.questions[key]["goal"],"operation":step["op"],"inputs":args})
                for output in outputs:
                    newenv = dict(env)
                    if not match(step.get("bind",[]),output,newenv):
                        continue
                    entry = {"op":step["op"],"inputs":args,"outputs":output}
                    self.queue.append(("advance",(key,rid,newenv,i+1,trace+[entry])))
        else:
            if self.all_proofs and not self.cutoffs:
                self.complete_through_steps = self.max_proof_steps
                self.enumeration_complete = not (self.excluded_by_size or self.depth_waiters)
        return self

    def proof_variants(self, goal):
        """Sort discovered acyclic derivations by size of their shared proof DAG."""
        if not self.all_proofs:
            raise ValueError('Proof enumeration was not enabled for this search')
        roots = sorted((a['proof'] for a in self.answers(goal)), key=lambda pid:len(self.proof_nodes[pid]))
        return [{'root':pid,'nodes':[self.proofs[node] for node in sorted(self.proof_nodes[pid],key=lambda p:int(p[1:]))]}
                for pid in roots]

    def export_nodes(self, roots):
        selected = set()
        pending = [pid for pid in roots if pid]
        while pending:
            pid = pending.pop()
            if pid in selected:
                continue
            selected.add(pid)
            pending.extend(step['proof'] for step in self.proofs[pid]['steps'] if 'proof' in step)
        return [node for pid,node in self.proofs.items() if pid in selected]

    def stats(self):
        return {"jobs":self.processed,"questions":len(self.questions),"applications":self.applications,
                "completed_facts":len(self.proofs),"queued_jobs":len(self.queue)+len(self.deferred),
                "pruned_truth_jobs":self.skipped_truth,"cutoffs":sorted(self.cutoffs)}
