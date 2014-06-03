@{
    ViewBag.Title = "Manage Departments";
    Layout = "~/Views/Shared/_Folder.cshtml";

    Bundles.Reference("scripts/custom/department/department.js", "custom");
    Bundles.Reference("content/custom/department.less", "custom");
}


<div id="viewArea">
    <div class="page-header">
        <h2>Departments <a href="#" class="btn btn-inverse" data-bind="click: $root.addDepartment"><i class="icon-plus"></i>&nbsp;Add</a></h2>
    </div>

    <div data-bind="template: {name: templateToUse, foreach: departments}"></div>
</div>

<script id="itemTmpl" type="text/html">
    <div class="row-fluid">
        <div class="span12 editable">

            <div style="padding: 10px">
                <h4 style="display: inline" data-bind="text: Name, click: $root.editDepartment"></h4>
                <span style="font-style: italic;" data-bind="text: Description, click: $root.editDepartment"></span>
            </div>

            <table class="table table-bordered table-striped">
                <thead>
                    <tr data-bind="visible: $data.Categories().length > 0 && $data.Categories()[0].Id() > 0">
                        <th style="width: 35%">Name</th>
                        <th>Description</th>
                    </tr>
                </thead>
                <tbody data-bind="template: {name: $root.tmplToUse, foreach: Categories}"></tbody>
                <tfoot>
                    <tr data-bind="visible: $root.selectedCategory() == null">
                        <td colspan="2">
                            <a class="btn btn-primary" data-bind="click: $root.addCategory">Add a Category</a>
                        </td>
                    </tr>
                </tfoot>
            </table>
        </div>
    </div>

</script>

<script id="editTmpl" type="text/html">
    <div class="row-fluid well" style="margin-bottom: 20px;">
        <div class="span12">
            <p>
                <input type="text" data-bind="value: Name" class="span12" placeholder="Enter Department Name" />
            </p>
            <span>
                <textarea data-bind="value:Description" placeholder="Enter Department Description" class="span12"></textarea></span>
        </div>
        <div>
            <a class="btn btn-success" data-bind="click: $root.saveDepartment" href="#" title="save"><i class="icon-ok"></i>&nbsp;Save</a>
            or 
            <a data-bind="click: $root.cancel" href="#" title="cancel">Cancel</a>
            <a class="btn btn-medium btn-warning pull-right" data-bind="click: $root.confirmDeleteDepartment, visible: $root.selectedItem().Id() > 0" href="#" title="remove"><i class="icon-trash"></i>&nbsp;Delete Department</a>
        </div>
    </div>
</script>

<script id="categoryTmpl" type="text/html">
    <tr data-bind="click: function(){$root.editCategory($parent, this);}">
        <td data-bind="text: Name"></td>
        <td data-bind="text: Description"></td>
    </tr>

</script>

<script id="editCategory" type="text/html">
    <tr style="background-color: #efefef">
        <td colspan="2">
            <input type="text" data-bind="value: Name" class="span12" placeholder="Category Name" /><br />
            <textarea data-bind="value:Description" class="span12" placeholder="Category Description"></textarea>
            <br />
            <div class="categoryControls">
                <a class="btn btn-medium btn-success" data-bind="click: $root.saveCategory" href="#" title="edit"><i class="icon-ok"></i>&nbsp;Save Category</a>
                or
                <a data-bind="click: $root.cancelCategory" href="#" title="remove">Cancel</a>
                <a class="btn btn-medium btn-warning pull-right" data-bind="click: function(){$root.confirmDeleteCategory($parent, this);}, visible: $root.selectedCategory().Id() > 0" href="#" title="remove"><i class="icon-trash"></i>&nbsp;Delete Category</a>
            </div>
        </td>
    </tr>
</script>
