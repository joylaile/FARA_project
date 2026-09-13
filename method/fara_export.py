"""Use the existing public compiled-plan interface; no new checker logic."""


def export(spec, engine):
    return engine.plan_view(engine.compile_contract(spec))
