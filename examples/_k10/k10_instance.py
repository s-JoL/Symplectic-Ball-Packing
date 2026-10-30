"""Frozen k=10, epsilon=0.1 metadata; no general-parameter model."""
import json
from pathlib import Path
from types import SimpleNamespace


class K10Instance:
    def __init__(self,verified_normal=False):
        data=json.loads(Path(__file__).with_name('data.json').read_text())['numeric']
        self.parameters=SimpleNamespace(**data['parameters'])
        self.path=SimpleNamespace(data=data['path'])
        self.sigma=data['sigma']
        self.model=SimpleNamespace(
            ball_layer=SimpleNamespace(starts=data['starts'],width=data['width']),
            cell_search_bound=lambda:data['cell_bound'])
