@model dynamic
@{
    ViewBag.Title = "title";
    Layout = "~/Views/Shared/_Folder.cshtml";
    ViewBag.SitemapProvider = "Modules";
}

<div class="row-fluid">
    <ul class="nav nav-tabs">
        <li class="active"><a href="#todo" data-toggle="tab"><i class="icon-align-justify"></i>Activity Feed</a> </li>
        <li><a href="#calendar" data-toggle="tab"><i class="icon-th-list"></i>My Upline</a></li>
        <li><a href="#calendar" data-toggle="tab"><i class="icon-th-list"></i>My Downline</a></li>
        <li><a href="#calendar" data-toggle="tab"><i class="icon-question-sign"></i>Questions</a></li>
    </ul>
    <div class="tab-content">
        <div class="tab-pane active" id="todo">
            @Html.Partial("_ActivityFeed")
        </div>
        <div class="tab-pane" id="calendar">
            <img src="../../Content/images/tree.PNG" />
        </div>
    </div>
</div>
