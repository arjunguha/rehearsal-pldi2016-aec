@{
    ViewBag.Title = "Index";
    ViewBag.SitemapProvider = "Modules";
    Layout = "~/Views/Shared/_Folder.cshtml";
}

<ul class="nav nav-tabs">
    <li class="active"><a href="#info" data-toggle="tab"><i class="icon-user"></i> Lead Information</a></li>
    <li><a href="#order" data-toggle="tab">Order Details</a></li>
    <li><a href="#history" data-toggle="tab">History</a></li>
    <li><a href="#actions" data-toggle="tab">Actions</a></li>
</ul>


<div class="tab-content">
  <div class="tab-pane active" id="info">@Html.Partial("_LeadInformation")</div>
  <div class="tab-pane" id="order">@Html.Partial("_OrderDetails")</div>
  <div class="tab-pane" id="history">@Html.Partial("_History")</div>
  <div class="tab-pane" id="actions">@Html.Partial("_Actions")</div>
</div>