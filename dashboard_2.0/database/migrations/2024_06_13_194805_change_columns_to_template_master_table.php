<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::table('template_master', function (Blueprint $table) {
            if(!Schema::hasColumn('template_master', 'subject'))
            {
                $table->string('subject')->nullable();
            }
            if(!Schema::hasColumn('template_master', 'to'))
            {
                $table->string('to')->nullable();
            }
            if(!Schema::hasColumn('template_master', 'bcc'))
            {
                $table->string('bcc')->nullable();
            }
            if(!Schema::hasColumn('template_master', 'cc'))
            {
                $table->string('cc')->nullable();
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('template_master', function (Blueprint $table) {
            $table->string('subject')->nullable()->change();
            $table->string('to')->nullable()->change();
            $table->string('bcc')->nullable()->change();
            $table->string('cc')->nullable()->change();
        });
    }
};
