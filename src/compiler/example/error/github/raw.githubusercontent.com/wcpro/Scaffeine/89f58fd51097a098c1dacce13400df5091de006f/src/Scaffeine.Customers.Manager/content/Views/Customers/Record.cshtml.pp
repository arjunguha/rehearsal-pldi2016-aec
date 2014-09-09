@{
    ViewBag.Title = "Index";
    ViewBag.SitemapProvider = "Modules";
    Layout = "~/Views/Shared/_Folder.cshtml";
}
@model $rootnamespace$.Core.Model.Customer
<div class="btn-group pull-right">
    <a class="btn dropdown-toggle btn-inverse" data-toggle="dropdown" href="#">Action <span class="caret">
    </span></a>
    <ul class="dropdown-menu">
        <li><a id="delete-lead" role="button" data-toggle="modal" href="#myModal">Delete</a></li>
    </ul>
</div>
<ul class="nav nav-tabs">
    <li class="active"><a href="#info" data-toggle="tab">Customer
        Information</a></li>
</ul>
<div class="tab-content">
    <div class="tab-pane active" id="info">@Html.Partial("_Details", Model)</div>
</div>
<form action="@Url.Action("Delete")" method="POST">
<div class="modal" id="myModal" tabindex="-1" role="dialog" aria-labelledby="myModalLabel"
    aria-hidden="true" style="display: none">
    @Html.HiddenFor(x => x.Id)
    <div class="modal-header">
        <button type="button" class="close" data-dismiss="modal" aria-hidden="true">
            ×</button>
        <h3 id="myModalLabel">
            Are you sure you want to delete?</h3>
    </div>
    <div class="modal-body">
        <p>
            Are you sure you want to delete this record?</p>
    </div>
    <div class="modal-footer">
        <button class="btn" data-dismiss="modal" aria-hidden="true">
            Cancel</button>
        <input type="submit" class="btn btn-warning" value="Yes, Delete this record" />
    </div>
</div>
</form>
@section Scripts
{
}
