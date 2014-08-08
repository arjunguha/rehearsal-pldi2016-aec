@{
	ViewBag.Title = "Dashboard";    
    Bundles.Reference("content/custom/hide-breadcrumb.less", "custom");
}

<div class="row-fluid">
    <ul class="nav nav-tabs">
        <li class="active">
            <a href="#todo" data-toggle="tab">
                To-Do List
            </a> 
        </li>
        <li>
            <a href="#calendar" data-toggle="tab">
                Calendar
            </a>
        </li>
    </ul>
    <div class="tab-content">
        <div class="tab-pane active" id="todo">
            @Html.Partial("_TodoPartial")
        </div>
        <div class="tab-pane" id="calendar">
            @Html.Partial("_Calendar")
        </div>
    </div>
</div>