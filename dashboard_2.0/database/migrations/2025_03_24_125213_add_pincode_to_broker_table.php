<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up()
    {
        if (Schema::hasTable('broker') && !Schema::hasColumn('broker', 'pincode')) {
            Schema::table('broker', function (Blueprint $table) {
                $table->string('pincode', 10)->nullable()->after('state');
            });
        }
    }

    public function down()
    {
        if (Schema::hasTable('broker') && Schema::hasColumn('broker', 'pincode')) {
            Schema::table('broker', function (Blueprint $table) {
                $table->dropColumn('pincode');
            });
        }
    }


};
